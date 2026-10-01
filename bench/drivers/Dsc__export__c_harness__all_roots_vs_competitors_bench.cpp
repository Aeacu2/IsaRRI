// 🔴 THE `ours` ARM HERE IS *NOT* THE SHIPPED SOLVER (corrected 2026-08-02).
// It is `all_dsc_carried_split_main` — Kioustelidis bound + split + dsc_CREDIT_main — which was
// RETIRED at R-3 and is absent from the current export:
//     grep -c 'define.*@all_dsc_carried_split_main' Dsc/export/dsc_adaptive.ll   -> 0
// This file's comment used to call it "our verified flagship". That was true before R-3 and is now
// false; it caused a benchmark result to be reported as the shipped solver's on 2026-08-01
// (docs/SOLVER_MISCOUNTS_2026-08-01.md §5b). The shipped flagship is `all_dsc_adaptive_main`,
// reachable as entry "hybrid" in suite_v2_bench.cpp — use suite_v2_bench_post, not this harness,
// for any claim about the shipped code. ⚠️ `all_dsc_carried_split_main` is also the function in
// docs/PITFALLS.md's 2026-07-10 entry (returned 5 roots vs 6 from five independent solvers).
//
// All-roots (no fixed search interval) comparison: the legacy carried/split
// all-roots pipeline (all_dsc_carried_split_main: Kioustelidis bound + split +
// dsc_CREDIT_main solve, all inside Sepref-synthesized/proven code) vs Z3's
// and msolve's OWN all-roots entry points (upolynomial::manager::isolate_roots
// and usolve's real_roots), each computing its own root bound internally --
// unlike z3_vs_llvm_root_bench.cpp, which fixes a shared search interval for
// a strict same-interval comparison. This harness instead measures the
// realistic "just isolate all real roots of this polynomial" usage mode.
//
// Standalone binary: does NOT include ../dsc_gmp_scalar.h (the stale full
// public export) or any OTHER generated Dsc .h -- only
// checks/Split_Export/dsc_gmp_split_export_check.h, whose gmp_mpz_struct
// definition is the one used throughout this file (per-file struct redefinition
// collisions are why the project's other harnesses stay in separate binaries).
#include <assert.h>
#include <gmpxx.h>
#include <stdint.h>

#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "math/polynomial/algebraic_numbers.h"
#include "math/polynomial/polynomial.h"
#include "math/polynomial/upolynomial.h"
#include "util/memory_manager.h"
#include "util/mpbq.h"
#include "util/rlimit.h"

extern "C" {
#include "../../checks/Split_Export/dsc_gmp_split_export_check.h"
#include "msolve/msolve-data.h"
#include "usolve/libusolve.h"
#include "upolynomial.h"
#include "algebraic_number.h"
#include "integer.h"
#include <flint/fmpz_poly.h>
#include <flint/arb_fmpz_poly.h>
#include <flint/acb.h>
}

static_assert(sizeof(gmp_mpz_struct) == sizeof(__mpz_struct),
              "Generated GMP struct layout does not match linked GMP");

static gmp_mpz_struct *as_gmp_ptr(mpz_class &x) {
  return reinterpret_cast<gmp_mpz_struct *>(x.get_mpz_t());
}
static gmp_mpz_struct *as_gmp_ptr_const(const mpz_class &x) {
  return reinterpret_cast<gmp_mpz_struct *>(
      const_cast<__mpz_struct *>(x.get_mpz_t()));
}

struct Poly {
  std::vector<mpz_class> coeffs;
  std::vector<gmp_mpz_struct *> ptrs;
  explicit Poly(std::vector<mpz_class> c) : coeffs(std::move(c)) {
    while (coeffs.size() > 1 && coeffs.back() == 0) coeffs.pop_back();
    ptrs.reserve(coeffs.size());
    for (const mpz_class &c2 : coeffs) ptrs.push_back(as_gmp_ptr_const(c2));
  }
};

// Same generators as z3_vs_llvm_root_bench.cpp / verified_split_bench.cpp, so
// results are directly comparable to the project's other benchmark tables.
static mpz_class patterned_coeff(int bits, uint64_t seed, int index) {
  const int b = std::max(bits, 2);
  const mpz_class modulus = mpz_class(1) << (b + 1);
  const mpz_class half = mpz_class(1) << b;
  const mpz_class j = index + 1;
  const mpz_class s = static_cast<unsigned long>(seed + 17);
  const mpz_class t = j + static_cast<unsigned long>(seed % 97) + 3;
  const mpz_class seed1 = static_cast<unsigned long>(seed + 1);
  mpz_class raw = (s * j * j * j * j * j +
                   mpz_class(1103515245UL) * t * t * t +
                   mpz_class(12345UL) * (j + 11) * seed1) %
                  modulus;
  mpz_class v = raw - half;
  if (v == 0) v = (index % 2 == 0) ? 1 : -1;
  return v;
}

static Poly dense_pattern(int degree, int bits, uint64_t seed) {
  std::vector<mpz_class> coeffs(static_cast<size_t>(degree + 1));
  for (int i = 0; i <= degree; ++i) coeffs[static_cast<size_t>(i)] = patterned_coeff(bits, seed, i);
  if (coeffs.back() == 0) coeffs.back() = 1;
  return Poly(std::move(coeffs));
}

static Poly mignotte(int n, int tau) {
  std::vector<mpz_class> c(static_cast<size_t>(n + 1), mpz_class(0));
  mpz_class a = mpz_class(1) << tau;
  c[0] = -2;
  c[1] = 4 * a;
  c[2] = -2 * a * a;
  c[static_cast<size_t>(n)] = 1;
  return Poly(std::move(c));
}

// NON-DYADIC cluster center (a = 2^tau - 1): mignotte() above puts the root pair's
// center at the exactly-dyadic point 2^-tau, accidentally easy (depth ~tau) for
// every bisection solver -- one coefficient bit changes runtime 100-1500x. This
// variant forces the canonical depth Theta(n*tau/2). ALWAYS include alongside the
// dyadic mignotte() for cluster/Mignotte-regime comparisons. See
// benchmark_results/summaries/mignotte_dyadic_center_rootcause_2026-07-09.md.
static Poly mignotte_true(int n, int tau) {
  std::vector<mpz_class> c(static_cast<size_t>(n + 1), mpz_class(0));
  mpz_class a = (mpz_class(1) << tau) - 1;
  c[0] = -2;
  c[1] = 4 * a;
  c[2] = -2 * a * a;
  c[static_cast<size_t>(n)] = 1;
  return Poly(std::move(c));
}

// --- our verified all-roots pipeline ---------------------------------------

static double time_ours(const Poly &p, int64_t out_cap, int64_t &count_out) {
  std::vector<mpz_class> pos_l(static_cast<size_t>(out_cap)), pos_r(static_cast<size_t>(out_cap)),
      neg_l(static_cast<size_t>(out_cap)), neg_r(static_cast<size_t>(out_cap));
  std::vector<gmp_mpz_struct *> pos_lp, pos_rp, neg_lp, neg_rp;
  std::vector<int64_t> pos_k(static_cast<size_t>(out_cap), -1),
      neg_k(static_cast<size_t>(out_cap), -1);
  for (int64_t i = 0; i < out_cap; ++i) {
    pos_lp.push_back(as_gmp_ptr(pos_l[static_cast<size_t>(i)]));
    pos_rp.push_back(as_gmp_ptr(pos_r[static_cast<size_t>(i)]));
    neg_lp.push_back(as_gmp_ptr(neg_l[static_cast<size_t>(i)]));
    neg_rp.push_back(as_gmp_ptr(neg_r[static_cast<size_t>(i)]));
  }
  int64_t pos_count = -1, neg_count = -1, xs0 = -1;

  const auto t0 = std::chrono::steady_clock::now();
  all_dsc_carried_split_main_check(
      &pos_count, pos_lp.data(), pos_rp.data(), pos_k.data(), &neg_count,
      neg_lp.data(), neg_rp.data(), neg_k.data(), &xs0, out_cap,
      static_cast<int64_t>(p.coeffs.size()),
      const_cast<gmp_mpz_struct **>(p.ptrs.data()));
  const auto t1 = std::chrono::steady_clock::now();

  if (pos_count < 0 || pos_count > out_cap) throw std::runtime_error("ours: pos count out of range");
  if (neg_count < 0 || neg_count > out_cap) throw std::runtime_error("ours: neg count out of range");
  count_out = pos_count + neg_count + (xs0 == 1 ? 1 : 0);
  return std::chrono::duration<double, std::milli>(t1 - t0).count();
}

// --- z3 upolynomial::manager::isolate_roots (bound-free) --------------------

struct Z3UPoly {
  reslimit rl;
  polynomial::numeral_manager nm;
  upolynomial::manager um;
  upolynomial::scoped_numeral_vector p;
  mpbq_manager bqm;

  explicit Z3UPoly(const Poly &poly) : um(rl, nm), p(um), bqm(nm) {
    for (const mpz_class &coeff : poly.coeffs) {
      upolynomial::numeral z;
      nm.set(z, coeff.get_str().c_str());
      p.push_back(z);
      nm.del(z);
    }
    um.trim(p);
  }
};

static double time_z3(Z3UPoly &zp, int64_t &count_out) {
  upolynomial::scoped_numeral_vector p_copy(zp.um);
  zp.um.set(zp.p.size(), zp.p.data(), p_copy);
  scoped_mpbq_vector roots(zp.bqm);
  scoped_mpbq_vector lowers(zp.bqm);
  scoped_mpbq_vector uppers(zp.bqm);

  const auto t0 = std::chrono::steady_clock::now();
  zp.um.isolate_roots(p_copy.size(), p_copy.data(), zp.bqm, roots, lowers, uppers);
  const auto t1 = std::chrono::steady_clock::now();

  count_out = static_cast<int64_t>(roots.size() + lowers.size());
  return std::chrono::duration<double, std::milli>(t1 - t0).count();
}

// --- msolve usolve real_roots (bound-free) ----------------------------------

static double time_msolve(const Poly &p, int64_t &count_out) {
  const auto deg = static_cast<unsigned long>(p.coeffs.size() - 1);
  mpz_t *coeffs = static_cast<mpz_t *>(std::malloc(sizeof(mpz_t) * (deg + 1)));
  if (coeffs == nullptr) throw std::bad_alloc();
  for (unsigned long i = 0; i <= deg; ++i) mpz_init_set(coeffs[i], p.coeffs[i].get_mpz_t());

  unsigned long pos = 0;
  unsigned long neg = 0;

  const auto t0 = std::chrono::steady_clock::now();
  interval *roots = real_roots(coeffs, deg, &pos, &neg, -1, 1, 0);
  const auto t1 = std::chrono::steady_clock::now();

  const size_t count = static_cast<size_t>(pos + neg);
  for (size_t i = 0; i < count; ++i) mpz_clear(roots[i].numer);
  std::free(roots);
  for (unsigned long i = 0; i <= deg; ++i) mpz_clear(coeffs[i]);
  std::free(coeffs);

  count_out = static_cast<int64_t>(count);
  return std::chrono::duration<double, std::milli>(t1 - t0).count();
}

// --- libpoly lp_upolynomial_roots_isolate (bound-free; exact, Sturm-sequence-based) -----

static double time_libpoly(const Poly &p, int64_t &count_out) {
  const size_t deg = p.coeffs.size() - 1;
  std::vector<lp_integer_t> coeffs(deg + 1);
  for (size_t i = 0; i <= deg; ++i) {
    lp_integer_construct_from_string(lp_Z, &coeffs[i], p.coeffs[i].get_str().c_str(), 10);
  }
  lp_upolynomial_t *f = lp_upolynomial_construct(lp_Z, deg, coeffs.data());
  for (size_t i = 0; i <= deg; ++i) lp_integer_destruct(&coeffs[i]);

  const auto t0 = std::chrono::steady_clock::now();
  size_t n = static_cast<size_t>(lp_upolynomial_roots_count(f, nullptr));
  std::vector<lp_algebraic_number_t> roots(n > 0 ? n : 1);
  size_t roots_size = 0;
  lp_upolynomial_roots_isolate(f, roots.data(), &roots_size);
  const auto t1 = std::chrono::steady_clock::now();

  for (size_t i = 0; i < roots_size; ++i) lp_algebraic_number_destruct(&roots[i]);
  lp_upolynomial_delete(f);

  count_out = static_cast<int64_t>(roots_size);
  return std::chrono::duration<double, std::milli>(t1 - t0).count();
}

// --- FLINT/Arb arb_fmpz_poly_complex_roots (bound-free; ball-arithmetic, filter real) ---

static double time_flint_arb(const Poly &p, int64_t &count_out) {
  const slong deg = static_cast<slong>(p.coeffs.size() - 1);
  fmpz_poly_t f;
  fmpz_poly_init2(f, deg + 1);
  fmpz_t c;
  fmpz_init(c);
  for (slong i = 0; i <= deg; ++i) {
    fmpz_set_mpz(c, p.coeffs[static_cast<size_t>(i)].get_mpz_t());
    fmpz_poly_set_coeff_fmpz(f, i, c);
  }
  fmpz_clear(c);

  acb_ptr roots = _acb_vec_init(static_cast<slong>(deg));

  const auto t0 = std::chrono::steady_clock::now();
  arb_fmpz_poly_complex_roots(roots, f, 0, 64);
  const auto t1 = std::chrono::steady_clock::now();

  int64_t real_count = 0;
  for (slong i = 0; i < deg; ++i) {
    if (arb_is_zero(acb_imagref(&roots[i]))) ++real_count;
  }

  _acb_vec_clear(roots, deg);
  fmpz_poly_clear(f);

  count_out = real_count;
  return std::chrono::duration<double, std::milli>(t1 - t0).count();
}

// --- driver ------------------------------------------------------------------

static void bench_case(const std::string &name, const Poly &p, int reps) {
  const int64_t out_cap = static_cast<int64_t>(p.coeffs.size());
  double best_ours = 1e30, best_z3 = 1e30, best_msolve = 1e30, best_libpoly = 1e30,
         best_arb = 1e30;
  int64_t roots_ours = -1, roots_z3 = -1, roots_msolve = -1, roots_libpoly = -1, roots_arb = -1;

  for (int r = 0; r < reps; ++r) {
    int64_t c;
    double t = time_ours(p, out_cap, c);
    best_ours = std::min(best_ours, t);
    roots_ours = c;
  }
  for (int r = 0; r < reps; ++r) {
    Z3UPoly zp(p);
    int64_t c;
    double t = time_z3(zp, c);
    best_z3 = std::min(best_z3, t);
    roots_z3 = c;
  }
  for (int r = 0; r < reps; ++r) {
    int64_t c;
    double t = time_msolve(p, c);
    best_msolve = std::min(best_msolve, t);
    roots_msolve = c;
  }
  for (int r = 0; r < reps; ++r) {
    int64_t c;
    double t = time_libpoly(p, c);
    best_libpoly = std::min(best_libpoly, t);
    roots_libpoly = c;
  }
  for (int r = 0; r < reps; ++r) {
    int64_t c;
    double t = time_flint_arb(p, c);
    best_arb = std::min(best_arb, t);
    roots_arb = c;
  }

  std::cout << name << ",deg=" << (p.coeffs.size() - 1)
            << ",ours_roots=" << roots_ours << ",ours_ms=" << best_ours
            << ",z3_roots=" << roots_z3 << ",z3_ms=" << best_z3
            << ",msolve_roots=" << roots_msolve << ",msolve_ms=" << best_msolve
            << ",libpoly_roots=" << roots_libpoly << ",libpoly_ms=" << best_libpoly
            << ",arb_roots=" << roots_arb << ",arb_ms=" << best_arb
            << "\n";
  std::cout.flush();

  if (!(roots_ours == roots_z3 && roots_z3 == roots_msolve && roots_msolve == roots_libpoly &&
        roots_libpoly == roots_arb)) {
    std::cerr << "WARNING: root count mismatch on " << name << ": ours=" << roots_ours
              << " z3=" << roots_z3 << " msolve=" << roots_msolve
              << " libpoly=" << roots_libpoly << " arb=" << roots_arb << "\n";
  }
}

// TRUE (non-dyadic-center) Mignotte family: ours/Z3/msolve only, deliberately SKIPPING
// libpoly and Arb here. Both were confirmed (mignotte_dyadic_center_rootcause_2026-07-09.md)
// to blow up catastrophically on the deep, non-dyadic-center trees this family forces
// (libpoly: 22s+ at n=129,tau=64 and did not finish a 60s cap at tau=128; Arb similarly
// explodes on clustered roots) -- including them here would risk another multi-minute
// hang in what should be a routine benchmark run. Add them back explicitly (with a
// generous per-case timeout) only for a dedicated, supervised investigation.
static void bench_case_true_family(const std::string &name, const Poly &p, int reps) {
  const int64_t out_cap = static_cast<int64_t>(p.coeffs.size());
  double best_ours = 1e30, best_z3 = 1e30, best_msolve = 1e30;
  int64_t roots_ours = -1, roots_z3 = -1, roots_msolve = -1;

  for (int r = 0; r < reps; ++r) {
    int64_t c;
    double t = time_ours(p, out_cap, c);
    best_ours = std::min(best_ours, t);
    roots_ours = c;
  }
  for (int r = 0; r < reps; ++r) {
    Z3UPoly zp(p);
    int64_t c;
    double t = time_z3(zp, c);
    best_z3 = std::min(best_z3, t);
    roots_z3 = c;
  }
  for (int r = 0; r < reps; ++r) {
    int64_t c;
    double t = time_msolve(p, c);
    best_msolve = std::min(best_msolve, t);
    roots_msolve = c;
  }

  std::cout << name << ",deg=" << (p.coeffs.size() - 1)
            << ",ours_roots=" << roots_ours << ",ours_ms=" << best_ours
            << ",z3_roots=" << roots_z3 << ",z3_ms=" << best_z3
            << ",msolve_roots=" << roots_msolve << ",msolve_ms=" << best_msolve
            << "\n";
  std::cout.flush();

  if (!(roots_ours == roots_z3 && roots_z3 == roots_msolve)) {
    std::cerr << "WARNING: root count mismatch on " << name << ": ours=" << roots_ours
              << " z3=" << roots_z3 << " msolve=" << roots_msolve << "\n";
  }
}

// name -> thunk, in the same order main() used to run them unconditionally. A pure
// dispatch table -- no solver-timing code touched -- so an external driver can run
// ONE case per process invocation and impose a real per-case wall-clock timeout
// (this binary has no internal alarm/timeout of its own; Arb and libpoly are
// data-dependent and can run for minutes on the deep dyadic-Mignotte cases).
static void run_named_case(const std::string &name, int reps) {
  if (name == "dense_d128_b16") bench_case(name, dense_pattern(128, 16, 1), reps);
  else if (name == "dense_d256_b16") bench_case(name, dense_pattern(256, 16, 1), reps);
  else if (name == "dense_d512_b16") bench_case(name, dense_pattern(512, 16, 1), reps);
  else if (name == "dense_d1024_b16") bench_case(name, dense_pattern(1024, 16, 1), reps);
  else if (name == "dense_d512_b64") bench_case(name, dense_pattern(512, 64, 2), reps);
  else if (name == "mignotte_16_32") bench_case(name, mignotte(16, 32), reps);
  else if (name == "mignotte_32_64") bench_case(name, mignotte(32, 64), reps);
  else if (name == "mignotte_64_128") bench_case(name, mignotte(64, 128), reps);
  else if (name == "mignotte_32_128") bench_case(name, mignotte(32, 128), reps);
  else if (name == "mignotte_24_200") bench_case(name, mignotte(24, 200), reps);
  else if (name == "mignotte_true_16_32")
    bench_case_true_family(name, mignotte_true(16, 32), reps);
  else if (name == "mignotte_true_32_64")
    bench_case_true_family(name, mignotte_true(32, 64), reps);
  else {
    std::cerr << "unknown case: " << name << "\n";
    std::exit(2);
  }
}

// Poly for a case name, or throws -- used by --only-solver, which needs the raw
// polynomial (not the whole bench_case bundling) to time exactly one solver.
static Poly resolve_poly(const std::string &name) {
  if (name == "dense_d128_b16") return dense_pattern(128, 16, 1);
  if (name == "dense_d256_b16") return dense_pattern(256, 16, 1);
  if (name == "dense_d512_b16") return dense_pattern(512, 16, 1);
  if (name == "dense_d1024_b16") return dense_pattern(1024, 16, 1);
  if (name == "dense_d512_b64") return dense_pattern(512, 64, 2);
  if (name == "mignotte_16_32") return mignotte(16, 32);
  if (name == "mignotte_32_64") return mignotte(32, 64);
  if (name == "mignotte_64_128") return mignotte(64, 128);
  if (name == "mignotte_32_128") return mignotte(32, 128);
  if (name == "mignotte_24_200") return mignotte(24, 200);
  if (name == "mignotte_true_16_32") return mignotte_true(16, 32);
  if (name == "mignotte_true_32_64") return mignotte_true(32, 64);
  std::cerr << "unknown case: " << name << "\n";
  std::exit(2);
}

// --only-solver <case> <solver> [reps]: time exactly ONE solver on ONE case, min-of-reps,
// single output line "<name>,<solver>_roots=R,<solver>_ms=T". Lets an external driver
// isolate which solver is the slow outlier on a case instead of losing every solver's
// number (including the fast ones) to one shared per-case timeout.
static void run_named_solver(const std::string &name, const std::string &solver, int reps) {
  const Poly p = resolve_poly(name);
  const int64_t out_cap = static_cast<int64_t>(p.coeffs.size());
  double best = 1e30;
  int64_t roots = -1;
  for (int r = 0; r < reps; ++r) {
    int64_t c;
    double t;
    if (solver == "ours") t = time_ours(p, out_cap, c);
    else if (solver == "z3") { Z3UPoly zp(p); t = time_z3(zp, c); }
    else if (solver == "msolve") t = time_msolve(p, c);
    else if (solver == "libpoly") t = time_libpoly(p, c);
    else if (solver == "arb") t = time_flint_arb(p, c);
    else { std::cerr << "unknown solver: " << solver << "\n"; std::exit(2); }
    best = std::min(best, t);
    roots = c;
  }
  std::cout << name << "," << solver << "_roots=" << roots
             << "," << solver << "_ms=" << best << "\n";
  std::cout.flush();
}

// --solve-stdin <name> <solver> [reps]: like --only-solver, but the polynomial comes from
// STDIN as one line of comma-separated decimal coefficients (c0,c1,...,cn), instead of the
// hardcoded 12-case resolve_poly() table. Lets an external driver feed this binary any case
// from suite_v2_bench.cpp's own generators (via its --dump-coeffs mode) without duplicating
// or hand-porting every generator into this file. Argv is avoided for the coefficients
// themselves (some suite_v2 cases have thousands of wide coefficients -- comfortably under
// ARG_MAX, but stdin has no such ceiling to worry about at all).
static void run_solve_stdin(const std::string &name, const std::string &solver, int reps) {
  std::string line;
  if (!std::getline(std::cin, line)) {
    std::cerr << "--solve-stdin: no input line on stdin\n";
    std::exit(2);
  }
  std::vector<mpz_class> coeffs;
  size_t pos = 0;
  while (pos <= line.size()) {
    size_t comma = line.find(',', pos);
    std::string tok = line.substr(pos, comma == std::string::npos ? std::string::npos : comma - pos);
    if (!tok.empty()) coeffs.emplace_back(tok);
    if (comma == std::string::npos) break;
    pos = comma + 1;
  }
  if (coeffs.empty()) {
    std::cerr << "--solve-stdin: parsed zero coefficients\n";
    std::exit(2);
  }
  const Poly p(std::move(coeffs));
  const int64_t out_cap = static_cast<int64_t>(p.coeffs.size());
  double best = 1e30;
  int64_t roots = -1;
  for (int r = 0; r < reps; ++r) {
    int64_t c;
    double t;
    if (solver == "ours") t = time_ours(p, out_cap, c);
    else if (solver == "z3") { Z3UPoly zp(p); t = time_z3(zp, c); }
    else if (solver == "msolve") t = time_msolve(p, c);
    else if (solver == "libpoly") t = time_libpoly(p, c);
    else if (solver == "arb") t = time_flint_arb(p, c);
    else { std::cerr << "unknown solver: " << solver << "\n"; std::exit(2); }
    best = std::min(best, t);
    roots = c;
  }
  std::cout << name << "," << solver << "_roots=" << roots
             << "," << solver << "_ms=" << best << "\n";
  std::cout.flush();
}

// --solve-stdin-multi <name> <solver>: SMT-BENCH Phase 2 companion to --solve-stdin. Reads
// MANY polynomials from stdin -- one per line, dump-format ("A\t<deg>\t<c0>,<c1>,...") or
// bare comma list -- and runs the solver once per poly IN-PROCESS, summing ms and roots.
// One process per (instance, solver) instead of N processes: per-poly process startup would
// dominate the heavy SMT instances. The runner's subprocess cap is the sole supervisor.
// Output: one "P\t<idx>\t<deg>\t<roots>\t<ms>" line per polynomial (1-based idx in input
// order), then "<name>,<solver>_roots=<R>,<solver>_ms=<T>,polys=<N>".
static int run_solve_stdin_multi(const std::string &name, const std::string &solver) {
  std::string line;
  double total_ms = 0.0;
  int64_t total_roots = 0;
  unsigned npolys = 0;
  std::string poly_lines;  // per-poly rows, emitted once before the summary line
  while (std::getline(std::cin, line)) {
    if (line.empty()) continue;
    std::string coeff_line = line;
    size_t tab = line.find('\t');
    if (tab != std::string::npos && line.compare(0, 1, "A") == 0) {
      size_t tab2 = line.find('\t', tab + 1);
      if (tab2 == std::string::npos) continue;
      coeff_line = line.substr(tab2 + 1);
    } else if (tab != std::string::npos) {
      continue;
    }
    std::vector<mpz_class> coeffs;
    size_t pos = 0;
    while (pos <= coeff_line.size()) {
      size_t comma = coeff_line.find(',', pos);
      std::string tok = coeff_line.substr(
          pos, comma == std::string::npos ? std::string::npos : comma - pos);
      if (!tok.empty()) coeffs.emplace_back(tok);
      if (comma == std::string::npos) break;
      pos = comma + 1;
    }
    if (coeffs.empty()) continue;
    const Poly p(std::move(coeffs));
    const int64_t out_cap = static_cast<int64_t>(p.coeffs.size());
    int64_t c = -1;
    double t;
    if (solver == "msolve") t = time_msolve(p, c);
    else if (solver == "libpoly") t = time_libpoly(p, c);
    else if (solver == "z3") { Z3UPoly zp(p); t = time_z3(zp, c); }
    else if (solver == "arb") t = time_flint_arb(p, c);
    else {
      std::cerr << "--solve-stdin-multi: unknown solver '" << solver << "'\n";
      std::exit(2);
    }
    poly_lines += "P\t" + std::to_string(npolys + 1) + "\t" +
                  std::to_string(static_cast<int64_t>(p.coeffs.size()) - 1) + "\t" +
                  std::to_string(c) + "\t" + std::to_string(t) + "\n";
    total_ms += t;
    total_roots += c;
    ++npolys;
  }
  if (npolys == 0) {
    std::cerr << "--solve-stdin-multi: no polynomials parsed\n";
    std::exit(2);
  }
  std::cout << poly_lines << name << "," << solver << "_roots=" << total_roots
            << "," << solver << "_ms=" << total_ms << ",polys=" << npolys << "\n";
  std::cout.flush();
  return 0;
}

int main(int argc, char **argv) {
  memory::initialize(0);
  std::cout.setf(std::ios::unitbuf);

  // --solve-stdin-multi <name> <solver>: see run_solve_stdin_multi() above.
  if (argc > 1 && std::string(argv[1]) == "--solve-stdin-multi") {
    if (argc < 4) {
      std::cerr << "usage: --solve-stdin-multi <name> <solver> < poly_lines\n";
      return 2;
    }
    return run_solve_stdin_multi(argv[2], argv[3]);
  }

  // --solve-stdin <name> <solver> [reps]: see run_solve_stdin() above.
  if (argc > 1 && std::string(argv[1]) == "--solve-stdin") {
    if (argc < 4) { std::cerr << "usage: --solve-stdin <name> <solver> [reps] < coeffs_line\n"; return 2; }
    const int reps = argc > 4 ? std::atoi(argv[4]) : 3;
    run_solve_stdin(argv[2], argv[3], reps);
    return 0;
  }

  // --only <case> [reps]: run a single named case (for external per-case timeout
  // supervision) instead of the full fixed sequence.
  if (argc > 1 && std::string(argv[1]) == "--only") {
    if (argc < 3) { std::cerr << "usage: --only <case> [reps]\n"; return 2; }
    const int reps = argc > 3 ? std::atoi(argv[3]) : 7;
    run_named_case(argv[2], reps);
    return 0;
  }

  // --only-solver <case> <solver> [reps]: time one solver on one case.
  if (argc > 1 && std::string(argv[1]) == "--only-solver") {
    if (argc < 4) { std::cerr << "usage: --only-solver <case> <solver> [reps]\n"; return 2; }
    const int reps = argc > 4 ? std::atoi(argv[4]) : 7;
    run_named_solver(argv[2], argv[3], reps);
    return 0;
  }

  const int reps = argc > 1 ? std::atoi(argv[1]) : 7;

  std::cout << "# ALL-ROOTS comparison (no fixed search interval; each solver computes its\n"
               "# own root bound internally): ours = all_dsc_carried_split_main (verified,\n"
               "# Kioustelidis bound + split + dsc_CREDIT_main solve), z3 =\n"
               "# upolynomial::manager::isolate_roots, msolve = usolve real_roots, libpoly =\n"
               "# lp_upolynomial_roots_isolate (exact, Sturm-sequence-based), arb = FLINT/Arb\n"
               "# arb_fmpz_poly_complex_roots filtered to real (ball-arithmetic numeric).\n"
               "# min-of-" << reps << ".\n";

  bench_case("dense_d128_b16", dense_pattern(128, 16, 1), reps);
  bench_case("dense_d256_b16", dense_pattern(256, 16, 1), reps);
  bench_case("dense_d512_b16", dense_pattern(512, 16, 1), reps);
  bench_case("dense_d1024_b16", dense_pattern(1024, 16, 1), reps);
  bench_case("dense_d512_b64", dense_pattern(512, 64, 2), reps);

  bench_case("mignotte_16_32", mignotte(16, 32), reps);
  bench_case("mignotte_32_64", mignotte(32, 64), reps);
  bench_case("mignotte_64_128", mignotte(64, 128), reps);
  bench_case("mignotte_32_128", mignotte(32, 128), reps);
  bench_case("mignotte_24_200", mignotte(24, 200), reps);

  // TRUE (non-dyadic-center) Mignotte family -- see mignotte_true()'s comment and
  // bench_case_true_family()'s. Kept modest in (n,tau): these already reach seconds
  // for msolve, not milliseconds, unlike the dyadic family at the same parameters.
  bench_case_true_family("mignotte_true_16_32", mignotte_true(16, 32), reps);
  bench_case_true_family("mignotte_true_32_64", mignotte_true(32, 64), reps);

  std::cout << "done\n";
  return 0;
}

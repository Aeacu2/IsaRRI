// z3_allroots_timer.cpp -- z3's all-roots isolator, timed exactly as the campaign harness times it,
// with a second arm that skips the squarefree decomposition.
//
// WHY THIS EXISTS (2026-09-18, thesis review). The thesis campaign timed z3 on SMT-BENCH through
// `upolynomial::manager::sqf_isolate_roots` (benchmark_results/smt_bench/z3_isolate_timer.cpp) but on
// MPSolve and AND-bench through `isolate_roots` (all_roots_vs_competitors_bench.cpp:time_z3), which is
// `square_free` (a gcd(P, P')) followed by `sqf_isolate_roots` (upolynomial.cpp:2529). Every input of
// both suites is squarefree (benchmark_results/{mpsolve_suite,and_bench}/sqfree_gate_2026-09-18.csv), and
// the other arms are excused that work (anewdsc -S 1; IsaRRI takes squarefreeness as a precondition).
// This driver re-times z3 on the call it would make on squarefree input, so that the thesis's z3
// column is measured the same way on all three suites.
//
// Interface: identical to all_roots_vs_competitors_bench's --solve-stdin, so scripts/final-suite-run.py
// drives it unchanged:
//     z3_allroots_timer --solve-stdin <name> <z3|z3sqf> <reps>   (coefficients c0,c1,... on stdin)
// prints "<name>,<solver>_roots=R,<solver>_ms=T" (min over reps). The polynomial construction
// (Z3UPoly) and the timed region are copied from all_roots_vs_competitors_bench.cpp:161-192 so that the
// `z3` arm here is the campaign's z3 arm; only the one call differs for `z3sqf`.
//
// Build (same vendored z3 as every other z3 driver; flags must match build/config.mk):
//   clang++ -std=c++20 -O2 -D_MP_INTERNAL -I third_party/z3_snapshot_20260612/src \
//       -I/opt/homebrew/include Dsc/export/c_harness/z3_allroots_timer.cpp \
//       third_party/z3_snapshot_20260612/build/libz3.a -L/opt/homebrew/lib -lgmpxx -lgmp \
//       -o Dsc/export/c_harness/build/z3_allroots_timer
#include <gmpxx.h>

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <iostream>
#include <string>
#include <vector>

#include "math/polynomial/upolynomial.h"
#include "util/mpbq.h"
#include "util/rlimit.h"

struct Z3UPoly {
  reslimit rl;
  polynomial::numeral_manager nm;
  upolynomial::manager um;
  upolynomial::scoped_numeral_vector p;
  mpbq_manager bqm;

  explicit Z3UPoly(const std::vector<mpz_class> &coeffs) : um(rl, nm), p(um), bqm(nm) {
    for (const mpz_class &coeff : coeffs) {
      upolynomial::numeral z;
      nm.set(z, coeff.get_str().c_str());
      p.push_back(z);
      nm.del(z);
    }
    um.trim(p);
  }
};

static double time_z3(Z3UPoly &zp, bool sqf, int64_t &count_out) {
  upolynomial::scoped_numeral_vector p_copy(zp.um);
  zp.um.set(zp.p.size(), zp.p.data(), p_copy);
  scoped_mpbq_vector roots(zp.bqm);
  scoped_mpbq_vector lowers(zp.bqm);
  scoped_mpbq_vector uppers(zp.bqm);

  const auto t0 = std::chrono::steady_clock::now();
  if (sqf)
    zp.um.sqf_isolate_roots(p_copy.size(), p_copy.data(), zp.bqm, roots, lowers, uppers);
  else
    zp.um.isolate_roots(p_copy.size(), p_copy.data(), zp.bqm, roots, lowers, uppers);
  const auto t1 = std::chrono::steady_clock::now();

  count_out = static_cast<int64_t>(roots.size() + lowers.size());
  return std::chrono::duration<double, std::milli>(t1 - t0).count();
}

int main(int argc, char **argv) {
  if (argc < 4 || std::string(argv[1]) != "--solve-stdin") {
    std::cerr << "usage: " << argv[0] << " --solve-stdin <name> <z3|z3sqf> [reps]\n";
    return 2;
  }
  const std::string name = argv[2], solver = argv[3];
  const int reps = argc > 4 ? std::max(1, std::atoi(argv[4])) : 1;
  if (solver != "z3" && solver != "z3sqf") {
    std::cerr << "unknown solver: " << solver << "\n";
    return 2;
  }
  std::string line;
  if (!std::getline(std::cin, line)) {
    std::cerr << "--solve-stdin: no input line on stdin\n";
    return 2;
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
    return 2;
  }
  double best = 1e30;
  int64_t roots = -1;
  for (int r = 0; r < reps; ++r) {
    int64_t c;
    Z3UPoly zp(coeffs);
    const double t = time_z3(zp, solver == "z3sqf", c);
    best = std::min(best, t);
    roots = c;
  }
  std::cout << name << "," << solver << "_roots=" << roots << "," << solver << "_ms=" << best << "\n";
  std::cout.flush();
  return 0;
}

// lib_dump.cpp -- the isolating intervals returned by the msolve, Z3 and libpoly arms, for the interval
// check (docs/LOGCF_PLAN_2026-10-08.md section 8). NOT a timing tool; the campaign's timed binaries are
// untouched. Each arm makes the call its timed harness makes:
//   msolve      real_roots(coeffs, deg, &pos, &neg, -1, 1, 0)        interval as msolve prints it
//   z3sqf       upolynomial::manager::sqf_isolate_roots              exact roots + (lower, upper) pairs
//   libpolysqf  lp_upolynomial_roots_isolate of libpoly_nosqf        dyadic interval or point
// stdout: "I\t<name>\t<idx>\t<left>\t<right>" per root (left = right for an exact root; rationals n/d),
//         "E\t<name>\t<idx>" after each polynomial.
// Usage: lib_dump <msolve|z3sqf|libpolysqf> stdin|stdin-multi <name>   (idx = ordinal of the "A" line)
// Build: see build_dumps.sh
#include <gmpxx.h>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>
#include "math/polynomial/upolynomial.h"
#include "util/mpbq.h"
#include "util/rlimit.h"
extern "C" {
#include "msolve/msolve-data.h"
#include "algebraic_number.h"
#include "integer.h"
#include "upolynomial.h"
interval *real_roots(mpz_t *upoly, unsigned long deg, unsigned long int *nb_pos_roots,
                     unsigned long int *nb_neg_roots, const int32_t precision, int nthrds, int info_level);
}
static std::string dy(const mpz_class &n, long k) {   // n / 2^k
  mpq_class q(n);
  if (k >= 0) q /= mpq_class(mpz_class(1) << k); else q *= mpq_class(mpz_class(1) << (-k));
  q.canonicalize();
  return q.get_str();
}
static void emit(const std::string &name, long idx, const std::string &l, const std::string &r) {
  std::printf("I\t%s\t%ld\t%s\t%s\n", name.c_str(), idx, l.c_str(), r.c_str());
}
static void do_msolve(const std::string &name, long idx, const std::vector<mpz_class> &cs) {
  unsigned long deg = cs.size() - 1, pos = 0, neg = 0;
  mpz_t *c = static_cast<mpz_t *>(std::malloc(sizeof(mpz_t) * (deg + 1)));
  for (unsigned long i = 0; i <= deg; ++i) mpz_init_set(c[i], cs[i].get_mpz_t());
  interval *roots = real_roots(c, deg, &pos, &neg, -1, 1, 0);
  for (unsigned long i = 0; i < pos + neg; ++i) {
    // msolve's own convention (usolve/print_usolve.c display_left/display_right):
    //   k > 0: [numer/2^k, (numer+1)/2^k];   k <= 0: [numer, numer + 2^(-k)]
    mpz_class n(roots[i].numer);
    const long k = roots[i].k;
    const std::string l = k > 0 ? dy(n, k) : dy(n, 0);
    emit(name, idx, l, roots[i].isexact ? l : (k > 0 ? dy(n + 1, k) : dy(n + (mpz_class(1) << (-k)), 0)));
  }
}
static void do_z3(const std::string &name, long idx, const std::vector<mpz_class> &cs) {
  reslimit rl;
  polynomial::numeral_manager nm;
  upolynomial::manager um(rl, nm);
  upolynomial::scoped_numeral_vector p(um);
  mpbq_manager bqm(nm);
  for (const mpz_class &coeff : cs) { upolynomial::numeral z; nm.set(z, coeff.get_str().c_str()); p.push_back(z); nm.del(z); }
  um.trim(p);
  scoped_mpbq_vector roots(bqm), lowers(bqm), uppers(bqm);
  um.sqf_isolate_roots(p.size(), p.data(), bqm, roots, lowers, uppers);
  auto s = [&](const mpbq &b) { return dy(mpz_class(nm.to_string(b.numerator())), b.k()); };
  for (unsigned i = 0; i < roots.size(); ++i) emit(name, idx, s(roots[i]), s(roots[i]));
  for (unsigned i = 0; i < lowers.size(); ++i) emit(name, idx, s(lowers[i]), s(uppers[i]));
}
static void do_libpoly(const std::string &name, long idx, const std::vector<mpz_class> &cs) {
  const size_t deg = cs.size() - 1;
  std::vector<lp_integer_t> coeffs(deg + 1);
  for (size_t i = 0; i <= deg; ++i) lp_integer_construct_from_string(lp_Z, &coeffs[i], cs[i].get_str().c_str(), 10);
  lp_upolynomial_t *f = lp_upolynomial_construct(lp_Z, deg, coeffs.data());
  std::vector<lp_algebraic_number_t> roots(deg > 0 ? deg : 1);
  size_t n = 0;
  lp_upolynomial_roots_isolate(f, roots.data(), &n);
  for (size_t i = 0; i < n; ++i) {
    const lp_dyadic_interval_t &I = roots[i].I;
    std::string a = dy(mpz_class(&I.a.a), (long)I.a.n);
    emit(name, idx, a, I.is_point ? a : dy(mpz_class(&I.b.a), (long)I.b.n));
  }
}
int main(int argc, char **argv) {
  if (argc != 4) return 2;
  const std::string solver = argv[1], mode = argv[2], name = argv[3];
  const bool multi = mode == "stdin-multi";
  std::string line;
  long idx = 0;
  while (std::getline(std::cin, line)) {
    std::string cl = line;
    if (multi) {
      if (line.compare(0, 2, "A\t") != 0) continue;
      ++idx;
      size_t t2 = line.find('\t', 2);
      if (t2 == std::string::npos) continue;
      cl = line.substr(t2 + 1);
    } else idx = 1;
    std::vector<mpz_class> cs;
    size_t pos = 0;
    while (pos <= cl.size()) {
      size_t comma = cl.find(',', pos);
      std::string tok = cl.substr(pos, comma == std::string::npos ? std::string::npos : comma - pos);
      if (!tok.empty()) cs.emplace_back(tok);
      if (comma == std::string::npos) break;
      pos = comma + 1;
    }
    while (cs.size() > 1 && cs.back() == 0) cs.pop_back();
    if (cs.size() >= 2) {
      if (solver == "msolve") do_msolve(name, idx, cs);
      else if (solver == "z3sqf") do_z3(name, idx, cs);
      else if (solver == "libpolysqf") do_libpoly(name, idx, cs);
      else return 2;
      std::printf("E\t%s\t%ld\n", name.c_str(), idx);
    }
    if (!multi) break;
  }
  return 0;
}

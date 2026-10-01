// bench_families.hpp -- suite v2 polynomial generators (docs/BENCHMARK_V2_AND_REEVALUATION_PLAN.md
// §3.2). Pure math: every generator returns a plain std::vector<mpz_class> (coefficient i =
// coeff of x^i, no trailing zero at the top degree), decoupled from any solver's generated
// gmp_mpz_struct header so this file is includable from both the five-flagship and the
// hybrid-only suite_v2_bench.cpp link targets.
//
// KEPT generators (moved verbatim in spirit from split_hybrid_only_bench.cpp -- same math, not
// "cleaned up"): patterned_coeff/dense_pattern, mignotte_true, wilkinson_poly, chebyshev_poly,
// geometric_offgrid_poly, nested_mignotte_poly, gaussian_clustered_poly, and their vmul_poly/
// vsub_poly/vx_pow_poly/vpow_poly/vsmult/vx_times helpers.
//
// NEW families (§3.2): kclu_pure, kclu_mig, iw/miw, sparse_rand, lac, res (Sylvester + Bareiss
// fraction-free elimination over Z[x]), mandel.
//
// Determinism: every generator with a `seed` parameter uses the splitmix64-derived `Rng` below;
// two calls with the same arguments produce byte-identical polynomials.
#ifndef DSC_BENCH_FAMILIES_HPP
#define DSC_BENCH_FAMILIES_HPP

#include <gmpxx.h>
#include <stdint.h>
#include <algorithm>
#include <cmath>
#include <cstdio>
#include <stdexcept>
#include <string>
#include <vector>

namespace bench_families {

using Poly = std::vector<mpz_class>;

// ---- deterministic RNG (splitmix64) ------------------------------------------------
struct Rng {
  uint64_t state;
  explicit Rng(uint64_t seed) : state(seed) {}
  uint64_t next_u64() {
    state += 0x9E3779B97F4A7C15ULL;
    uint64_t z = state;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    z ^= z >> 31;
    return z;
  }
  double next_double01() { return (static_cast<double>(next_u64() >> 11) + 0.5) * (1.0 / 9007199254740992.0); }
  double next_gauss() {
    double u1 = next_double01(), u2 = next_double01();
    return std::sqrt(-2.0 * std::log(u1)) * std::cos(2.0 * 3.14159265358979323846 * u2);
  }
  // uniform integer in [0, bound) -- bound must be > 0 and comfortably below 2^63
  int64_t next_below(int64_t bound) { return static_cast<int64_t>(next_u64() % static_cast<uint64_t>(bound)); }
};

// ---- generic poly helpers (over Z[x]) ---------------------------------------------
inline void trim(Poly &p) {
  while (p.size() > 1 && p.back() == 0) p.pop_back();
}
inline Poly vadd_poly(const Poly &a, const Poly &b) {
  Poly r(std::max(a.size(), b.size()));
  for (size_t i = 0; i < r.size(); ++i)
    r[i] = (i < a.size() ? a[i] : mpz_class(0)) + (i < b.size() ? b[i] : mpz_class(0));
  trim(r);
  return r;
}
inline Poly vsub_poly(const Poly &a, const Poly &b) {
  Poly r(std::max(a.size(), b.size()));
  for (size_t i = 0; i < r.size(); ++i)
    r[i] = (i < a.size() ? a[i] : mpz_class(0)) - (i < b.size() ? b[i] : mpz_class(0));
  trim(r);
  return r;
}
inline Poly vmul_poly(const Poly &a, const Poly &b) {
  if (a.empty() || b.empty()) return Poly{};
  Poly r(a.size() + b.size() - 1, mpz_class(0));
  for (size_t i = 0; i < a.size(); ++i)
    for (size_t j = 0; j < b.size(); ++j) r[i + j] += a[i] * b[j];
  trim(r);
  return r;
}
inline Poly vx_pow_poly(int n) {
  Poly r(static_cast<size_t>(n + 1), mpz_class(0));
  r[static_cast<size_t>(n)] = 1;
  return r;
}
inline Poly vpow_poly(Poly base, int exp) {
  Poly r{1};
  while (exp > 0) {
    if ((exp & 1) != 0) r = vmul_poly(r, base);
    exp >>= 1;
    if (exp > 0) base = vmul_poly(base, base);
  }
  return r;
}
inline Poly vsmult(const mpz_class &c, Poly p) {
  for (mpz_class &x : p) x *= c;
  trim(p);
  return p;
}
inline Poly vx_times(const Poly &p) {
  Poly r;
  r.reserve(p.size() + 1);
  r.push_back(mpz_class(0));
  r.insert(r.end(), p.begin(), p.end());
  return r;
}

// ============================== KEPT FAMILIES =======================================

inline mpz_class patterned_coeff(int bits, uint64_t seed, int index) {
  const int b = std::max(bits, 2);
  const mpz_class modulus = mpz_class(1) << (b + 1);
  const mpz_class half = mpz_class(1) << b;
  const mpz_class j = index + 1;
  const mpz_class s = static_cast<unsigned long>(seed + 17);
  const mpz_class t = j + static_cast<unsigned long>(seed % 97) + 3;
  const mpz_class seed1 = static_cast<unsigned long>(seed + 1);
  mpz_class raw = (s * j * j * j * j * j + mpz_class(1103515245UL) * t * t * t +
                   mpz_class(12345UL) * (j + 11) * seed1) % modulus;
  mpz_class v = raw - half;
  if (v == 0) v = (index % 2 == 0) ? 1 : -1;
  return v;
}
inline Poly dense_pattern(int degree, int bits, uint64_t seed) {
  Poly coeffs(static_cast<size_t>(degree + 1));
  for (int i = 0; i <= degree; ++i) coeffs[static_cast<size_t>(i)] = patterned_coeff(bits, seed, i);
  if (coeffs.back() == 0) coeffs.back() = 1;
  return coeffs;
}
inline Poly mignotte_true(int n, int tau) {
  Poly c(static_cast<size_t>(n + 1), mpz_class(0));
  mpz_class a = (mpz_class(1) << tau) - 1;
  c[0] = -2; c[1] = 4 * a; c[2] = -2 * a * a; c[static_cast<size_t>(n)] = 1;
  return c;
}
inline Poly wilkinson_poly(int n) {
  Poly p{1};
  for (int i = 1; i <= n; ++i) p = vmul_poly(p, Poly{-i, 1});
  return p;
}
inline Poly chebyshev_poly(int n) {
  Poly t0{1}, t1{0, 1};
  if (n == 0) return t0;
  if (n == 1) return t1;
  for (int k = 2; k <= n; ++k) {
    Poly t2 = vsub_poly(vsmult(2, vx_times(t1)), t0);
    t0 = std::move(t1);
    t1 = std::move(t2);
  }
  return t1;
}
inline Poly geometric_offgrid_poly(int n) {
  Poly p{1};
  mpz_class pw = 1;
  for (int i = 0; i < n; ++i) {
    p = vmul_poly(p, Poly{-(pw + 1), 1});
    pw *= 2;
  }
  return p;
}
inline Poly nested_mignotte_poly(int n, int tau) {
  if (n % 4 != 0 || n / 4 <= 16 || tau < 8) throw std::runtime_error("nested_mignotte_poly: bad parameters");
  const mpz_class a = (mpz_class(1) << (tau / 8)) - 1;
  const Poly q{-1, 0, a};
  Poly p{1};
  for (int i = 1; i <= 4; ++i) p = vmul_poly(p, vsub_poly(vx_pow_poly(n / 4), vpow_poly(q, 2 * i)));
  return p;
}
inline Poly gaussian_clustered_poly(int m, int scale_bits, uint64_t seed) {
  std::vector<double> logw(static_cast<size_t>(m + 1));
  double logwmax = -1e300;
  for (int i = 0; i <= m; ++i) {
    double lb = std::lgamma(m + 1.0) - std::lgamma(i + 1.0) - std::lgamma(m - i + 1.0);
    logw[static_cast<size_t>(i)] = 0.5 * lb - 0.5 * std::log(i + 1.0);
    logwmax = std::max(logwmax, logw[static_cast<size_t>(i)]);
  }
  Rng rng(seed);
  Poly f(static_cast<size_t>(m + 1));
  const int keep = 60;
  for (int i = 0; i <= m; ++i) {
    double g = rng.next_gauss();
    double rel = std::exp(logw[static_cast<size_t>(i)] - logwmax);
    double mant = g * rel;
    long long m60 = static_cast<long long>(std::llround(mant * (double)(1LL << keep)));
    mpz_class ci = mpz_class(static_cast<long>(m60));
    if (scale_bits > keep) ci <<= (scale_bits - keep);
    else ci >>= (keep - scale_bits);
    f[static_cast<size_t>(i)] = ci;
  }
  if (f.back() == 0) f.back() = mpz_class(1) << scale_bits;
  Poly ff = vmul_poly(f, f);
  ff[0] -= 1;
  return ff;
}

// ============================== NEW FAMILY 1: kclu ==================================

// kclu_pure_k{K}_tau{T}: P(x) = prod_{i=1}^{K} (D*x - (c+i)), D=2^T, c=(D/3)|1 (odd, non-dyadic).
// Exactly K real roots at (c+i)/D ~ 1/3, pairwise separation 2^-T, interior (far from both
// root-bound endpoints). Known root count = K.
inline Poly kclu_pure(int K, int T) {
  mpz_class D = mpz_class(1) << T;
  mpz_class c = (D / 3) | 1;
  Poly p{1};
  for (int i = 1; i <= K; ++i) p = vmul_poly(p, Poly{-(c + i), D});
  return p;
}

// kclu_mig_n{N}_k{K}_tau{T}: x^N - ((2^ceil(T/K) - 1)*x - 1)^K. Root count not closed-form.
inline Poly kclu_mig(int N, int K, int T) {
  int e = (T + K - 1) / K;
  mpz_class a = (mpz_class(1) << e) - 1;
  Poly q{-1, a};  // a*x - 1
  Poly qk = vpow_poly(q, K);
  return vsub_poly(vx_pow_poly(N), qk);
}

// ============================== NEW FAMILY 2: iw/miw =================================

// IW_n = prod_{i=1}^{n} (i*x - 1): exactly n real roots at 1/i, accumulating at 0+.
inline Poly iw_poly(int n) {
  Poly p{1};
  for (int i = 1; i <= n; ++i) p = vmul_poly(p, Poly{-1, i});
  return p;
}
// mIW_n = IW_n - 1 (perturbed, irrational roots -- the harder variant).
inline Poly miw_poly(int n) {
  Poly p = iw_poly(n);
  p[0] -= 1;
  return p;
}

// ============================== NEW FAMILY 3: sparse/lac ==============================

// sparse_rand_n{N}_t{T}: exactly T nonzero terms -- exponent 0, exponent N, and T-2 drawn
// uniformly WITHOUT replacement from (0,N); coefficients uniform +-(2^16-1), nonzero, seeded.
inline Poly sparse_rand(int n, int t, uint64_t seed) {
  if (t < 2) throw std::runtime_error("sparse_rand: t must be >= 2");
  Rng rng(seed);
  std::vector<bool> used(static_cast<size_t>(n + 1), false);
  std::vector<int> exps;
  exps.push_back(0);
  exps.push_back(n);
  used[0] = used[static_cast<size_t>(n)] = true;
  while (static_cast<int>(exps.size()) < t) {
    int cand = 1 + static_cast<int>(rng.next_below(n - 1));  // in [1, n-1]
    if (!used[static_cast<size_t>(cand)]) {
      used[static_cast<size_t>(cand)] = true;
      exps.push_back(cand);
    }
  }
  Poly p(static_cast<size_t>(n + 1), mpz_class(0));
  for (int e : exps) {
    int64_t mag = 1 + rng.next_below((1 << 16) - 1);  // 1..2^16-1
    bool neg = (rng.next_u64() & 1) != 0;
    p[static_cast<size_t>(e)] = static_cast<long>(neg ? -mag : mag);
  }
  return p;
}

// lac_n{N}: 1 + sum_{i=1}^{k} (-1)^i x^(i^2), k = floor(sqrt(N)). Near-zero real roots.
inline Poly lac_poly(int n) {
  int k = static_cast<int>(std::floor(std::sqrt(static_cast<double>(n))));
  Poly p(static_cast<size_t>(k * k + 1), mpz_class(0));
  p[0] = 1;
  for (int i = 1; i <= k; ++i) {
    mpz_class sign = (i % 2 == 0) ? 1 : -1;
    p[static_cast<size_t>(i * i)] = sign;
  }
  trim(p);
  return p;
}

// ============================== NEW FAMILY 5: mandel ==================================

// p_0 = 1, p_{k+1}(x) = x*p_k(x)^2 + 1. Fractal clustering, few real roots.
//
// PROVENANCE (the only family here with a non-synthetic source -- worth stating in Ch. 10, since
// every other family is a construction). These are the Gleason polynomials. Let q_1(c) = c,
// q_{n+1} = q_n^2 + c, whose roots are the centres of the period-dividing-n hyperbolic components
// of the Mandelbrot set (the c for which the critical point 0 is periodic under z |-> z^2 + c).
// Every q_n is divisible by c; writing q_n = c*r_n gives q_{n+1} = c*(c*r_n^2 + 1), i.e. exactly
// our recurrence with r_1 = 1. So p_k = r_{k+1} and q_{k+1} = x * p_k: the roots of p_k are the
// centres of period dividing k+1, MINUS the c = 0 centre that q_{k+1} carries as its extra root.
// Degrees agree: deg p_k = 2^k - 1 = deg q_{k+1} - 1. The coefficient growth and the root
// clustering are therefore dictated by complex dynamics, not chosen by us, and the real roots are
// the real-axis (antenna) centres -- hence "few real roots" at high degree.
//
// ⚠️ SQUAREFREENESS IS NOT ESTABLISHED HERE. That the Gleason polynomials are separable is a
// classical question (attributed to Gleason, usually argued 2-adically) and we have NOT verified
// it for the k we actually generate. Do not cite it as squarefree; our own solver's squarefree
// precondition is unchecked at runtime, so this family must go through the mechanical
// is_square_free gate before it can appear in a benchmark of record.
inline Poly mandel_poly(int k) {
  Poly p{1};
  for (int i = 0; i < k; ++i) {
    Poly sq = vmul_poly(p, p);
    p = vx_times(sq);
    p[0] += 1;
  }
  return p;
}

// ============================== NEW FAMILY 4: res (resultant/CAD) =====================
//
// res_d{D} = Res_y(f(x,y), g(x,y)), f,g random dense bivariate bidegree (D,D), coefficients
// uniform +-(2^10-1), fixed seed. Built as the (2D)x(2D) Sylvester matrix over the ring Z[x]
// (each matrix entry is itself a polynomial in x -- a y-coefficient of f or g), eliminated by
// classical Bareiss fraction-free Gaussian elimination (exact at every step: dividing by the
// previous pivot always yields a zero remainder over an integral domain -- Bareiss's theorem).
// A nonzero remainder at any step is a bug, not data: it aborts loudly.

using XPoly = std::vector<mpz_class>;  // a scalar of the ring Z[x]; canonical form: trimmed,
                                        // empty vector == the zero element

inline void xp_trim(XPoly &p) {
  while (!p.empty() && p.back() == 0) p.pop_back();
}
inline bool xp_is_zero(const XPoly &p) { return p.empty(); }
inline XPoly xp_add(const XPoly &a, const XPoly &b) {
  XPoly r(std::max(a.size(), b.size()), mpz_class(0));
  for (size_t i = 0; i < r.size(); ++i)
    r[i] = (i < a.size() ? a[i] : mpz_class(0)) + (i < b.size() ? b[i] : mpz_class(0));
  xp_trim(r);
  return r;
}
inline XPoly xp_sub(const XPoly &a, const XPoly &b) {
  XPoly r(std::max(a.size(), b.size()), mpz_class(0));
  for (size_t i = 0; i < r.size(); ++i)
    r[i] = (i < a.size() ? a[i] : mpz_class(0)) - (i < b.size() ? b[i] : mpz_class(0));
  xp_trim(r);
  return r;
}
inline XPoly xp_mul(const XPoly &a, const XPoly &b) {
  if (a.empty() || b.empty()) return XPoly{};
  XPoly r(a.size() + b.size() - 1, mpz_class(0));
  for (size_t i = 0; i < a.size(); ++i)
    for (size_t j = 0; j < b.size(); ++j) r[i + j] += a[i] * b[j];
  xp_trim(r);
  return r;
}
// Exact division A / B over Z[x] (B must divide A with zero remainder -- guaranteed by
// Bareiss's theorem when called correctly). Aborts loudly on a nonzero intermediate or final
// remainder rather than silently returning a wrong quotient.
inline XPoly xp_exact_div(XPoly a, const XPoly &b) {
  if (xp_is_zero(b)) throw std::runtime_error("xp_exact_div: division by the zero polynomial");
  if (xp_is_zero(a)) return XPoly{};
  XPoly q;
  const mpz_class &blead = b.back();
  const int bdeg = static_cast<int>(b.size()) - 1;
  while (!xp_is_zero(a) && static_cast<int>(a.size()) - 1 >= bdeg) {
    const mpz_class &alead = a.back();
    mpz_class qc;
    if (!mpz_divisible_p(alead.get_mpz_t(), blead.get_mpz_t()))
      throw std::runtime_error("xp_exact_div: non-exact leading-coefficient division -- Bareiss invariant broken");
    mpz_divexact(qc.get_mpz_t(), alead.get_mpz_t(), blead.get_mpz_t());
    const int shift = static_cast<int>(a.size()) - 1 - bdeg;
    if (static_cast<int>(q.size()) < shift + 1) q.resize(static_cast<size_t>(shift + 1), mpz_class(0));
    q[static_cast<size_t>(shift)] = qc;
    // a -= qc * x^shift * b
    for (size_t j = 0; j < b.size(); ++j) a[static_cast<size_t>(shift) + j] -= qc * b[j];
    xp_trim(a);
  }
  if (!xp_is_zero(a)) throw std::runtime_error("xp_exact_div: nonzero final remainder -- Bareiss invariant broken");
  xp_trim(q);
  return q;
}

// Generic Bareiss elimination over XPoly entries (in-place). Returns {determinant, singular}.
inline std::pair<XPoly, bool> det_bareiss(std::vector<std::vector<XPoly>> M) {
  const int n = static_cast<int>(M.size());
  if (n == 0) return {XPoly{1}, false};
  int sign = 1;
  XPoly prev_pivot{1};  // the "M[-1][-1] = 1" convention
  for (int k = 0; k < n - 1; ++k) {
    if (xp_is_zero(M[static_cast<size_t>(k)][static_cast<size_t>(k)])) {
      int piv = -1;
      for (int r = k + 1; r < n; ++r)
        if (!xp_is_zero(M[static_cast<size_t>(r)][static_cast<size_t>(k)])) { piv = r; break; }
      if (piv < 0) return {XPoly{}, true};  // singular: determinant == 0
      std::swap(M[static_cast<size_t>(k)], M[static_cast<size_t>(piv)]);
      sign = -sign;
    }
    for (int i = k + 1; i < n; ++i) {
      for (int j = k + 1; j < n; ++j) {
        XPoly num = xp_sub(xp_mul(M[static_cast<size_t>(k)][static_cast<size_t>(k)], M[static_cast<size_t>(i)][static_cast<size_t>(j)]),
                            xp_mul(M[static_cast<size_t>(i)][static_cast<size_t>(k)], M[static_cast<size_t>(k)][static_cast<size_t>(j)]));
        M[static_cast<size_t>(i)][static_cast<size_t>(j)] = xp_exact_div(num, prev_pivot);
      }
      M[static_cast<size_t>(i)][static_cast<size_t>(k)] = XPoly{};
    }
    prev_pivot = M[static_cast<size_t>(k)][static_cast<size_t>(k)];
  }
  XPoly result = M[static_cast<size_t>(n - 1)][static_cast<size_t>(n - 1)];
  if (sign < 0) result = xp_sub(XPoly{}, result);
  return {result, false};
}

// Res_y(f,g) via Bareiss elimination on the Sylvester matrix (f,g dense bidegree (D,D)).
// f/g given as vector<XPoly> of length D+1: f[i] = the y^i coefficient (a poly in x, degree<=D).
// Returns {resultant, singular}; on singular=true the caller should re-draw with a new seed.
inline std::pair<XPoly, bool> resultant_y(const std::vector<XPoly> &f, const std::vector<XPoly> &g, int D) {
  const int n = 2 * D;
  std::vector<std::vector<XPoly>> M(static_cast<size_t>(n), std::vector<XPoly>(static_cast<size_t>(n)));
  // f-block: rows 0..D-1; row i has f_D, f_{D-1}, ..., f_0 starting at column i
  for (int i = 0; i < D; ++i)
    for (int kk = 0; kk <= D; ++kk) M[static_cast<size_t>(i)][static_cast<size_t>(i + kk)] = f[static_cast<size_t>(D - kk)];
  // g-block: rows D..2D-1
  for (int i = 0; i < D; ++i)
    for (int kk = 0; kk <= D; ++kk) M[static_cast<size_t>(D + i)][static_cast<size_t>(i + kk)] = g[static_cast<size_t>(D - kk)];
  return det_bareiss(std::move(M));
}

// Builds a random dense bivariate poly, bidegree (D,D), coefficients uniform +-(2^bits - 1).
inline std::vector<XPoly> random_bivariate(int D, int bits, Rng &rng) {
  std::vector<XPoly> f(static_cast<size_t>(D + 1));
  for (int i = 0; i <= D; ++i) {
    XPoly row(static_cast<size_t>(D + 1));
    for (int j = 0; j <= D; ++j) {
      int64_t mag = 1 + rng.next_below((int64_t(1) << bits) - 1);
      bool neg = (rng.next_u64() & 1) != 0;
      row[static_cast<size_t>(j)] = static_cast<long>(neg ? -mag : mag);
    }
    xp_trim(row);
    f[static_cast<size_t>(i)] = row;
  }
  return f;
}

// res_d{D}: builds f,g and returns {resultant polynomial (in x), seed actually used}. Retries
// with seed+1, seed+2, ... on a singular draw (f,g sharing a factor) -- deterministic given the
// starting seed, and the returned seed must be recorded in the case table for reproducibility.
inline std::pair<Poly, uint64_t> res_poly(int D, uint64_t seed) {
  for (uint64_t attempt = 0; attempt < 16; ++attempt) {
    uint64_t s = seed + attempt;
    Rng rf(s), rg(s ^ 0x9E3779B97F4A7C15ULL);
    auto f = random_bivariate(D, 10, rf);
    auto g = random_bivariate(D, 10, rg);
    auto [res, singular] = resultant_y(f, g, D);
    if (!singular && !res.empty()) return {res, s};
  }
  throw std::runtime_error("res_poly: 16 consecutive singular draws -- something is wrong");
}

// ============ FINAL SUITE FAMILIES (docs/FINAL_BENCHMARK_SUITE.md §7, 2026-08-01) ============
//
// The 125-case suite adds the paper families we lacked: Chebyshev U, Hermite, Laguerre,
// Legendre, Wilkinson-like, gauss theta(log n) (uniform-coefficient f^2-1), Mignotte
// rational/irrational centres, dense tau=1024 (incl. monic / monic+trailing-1 variants),
// plus a resultant generator fixed to yield degree exactly D^2.
//
// Construction notes (matching the ANewDsc addendum page's captions where they are explicit):
//  - chebyshev T/U, wilkinson: as on the page. U_0=1, U_1=2x, U_{i+1}=2x U_i - U_{i-1}.
//  - laguerre: the division-free integer recurrence, i.e. n! * L_n (its max coefficient
//    bit length matches the page's bitsize column exactly: 743/1723/3933 at d128/256/512).
//  - hermite: physicists' H_n (2x H_n - 2n H_{n-1}). legendre: 2^n * P_n (first kind).
//    NOTE: the page's bitsize column reads ~2x the standard integer forms' max coefficient
//    for T/U/H/Lg (its "bitsize" convention differs per family; Laguerre matches exactly).
//    The ladder is anchored on measured difficulty, not on that column; the deviation is
//    documented in FINAL_BENCHMARK_SUITE.md §6 calibration notes.
//  - uniform_clustered: f = sum a_i x^i, a_i uniform in {-2^tau, ..., 2^tau}, return f^2-1.
//  - mignotte_rat/irr: x^n - ((2^ceil(tau/2)-1)x-1)^2 / x^n - ((2^ceil(tau/2)-1)x^2-1)^2
//    (the page's bitsize column IS tau for both; its irrational-centre caption reads 2^(tau/4)-1
//    but the table's column reads tau/2 of that internal tau, so parameterizing by the column
//    reproduces the table exactly).
//  - dense_uniform: coefficients uniform in {-2^tau, ..., 2^tau}, optional monic /
//    monic+trailing-1 (their tau=1024 family).
//  - wilkinson_like: prod_{i=1}^n ((n+1)x - i), the integer form of prod(x - i/(n+1)).
//  - res_dense_poly: Res_y(f,g) for f,g random DENSE BIVARIATE polys of TOTAL degree D,
//    monic in y (y^D coefficient 1, y^k coefficient an x-poly of degree <= D-k). This
//    triangle structure makes deg_x Res exactly D^2 (page's degree column; a full
//    bidegree-(D,D) Sylvester would give 2D^2 - D, both-monic, or 2D^2, non-monic --
//    verified by hand for D=2 and empirically at D=2/3/5/10).
//    The suite_v2-era res_poly (both non-monic, degree 2*D^2) is untouched.

// uniform integer in [0, 2^bits); bits > 62 handled by chunked draws (deterministic).
inline mpz_class uniform_bits(Rng &rng, int bits) {
  if (bits <= 62) return mpz_class(static_cast<long>(rng.next_below(int64_t(1) << bits)));
  mpz_class v = 0;
  int have = 0;
  while (have < bits) {
    int take = std::min(62, bits - have);
    v <<= take;
    v += static_cast<long>(rng.next_below(int64_t(1) << take));
    have += take;
  }
  return v;
}

inline Poly chebyshev_u_poly(int n) {
  Poly u0{1}, u1{0, 2};
  if (n == 0) return u0;
  if (n == 1) return u1;
  for (int k = 2; k <= n; ++k) {
    Poly u2 = vsub_poly(vsmult(2, vx_times(u1)), u0);
    u0 = std::move(u1);
    u1 = std::move(u2);
  }
  return u1;
}

inline Poly hermite_poly(int n) {
  Poly h0{1}, h1{0, 2};
  if (n == 0) return h0;
  if (n == 1) return h1;
  for (int k = 1; k < n; ++k) {
    Poly h2 = vsub_poly(vsmult(2, vx_times(h1)), vsmult(2 * k, h0));
    h0 = std::move(h1);
    h1 = std::move(h2);
  }
  return h1;
}

// n! * L_n via the division-free recurrence: L~_{k+1} = (2k+1 - x) L~_k - k^2 L~_{k-1}.
inline Poly laguerre_poly(int n) {
  Poly l0{1}, l1{1, -1};
  if (n == 0) return l0;
  if (n == 1) return l1;
  for (int k = 1; k < n; ++k) {
    Poly h2(l1.size() + 1, mpz_class(0));
    for (size_t i = 0; i < l1.size(); ++i) {
      h2[static_cast<size_t>(i)] += static_cast<long>(2 * k + 1) * l1[i];  // (2k+1) L~_k
      h2[static_cast<size_t>(i) + 1] -= l1[i];                             // - x * L~_k
    }
    for (size_t i = 0; i < l0.size(); ++i)
      h2[static_cast<size_t>(i)] -= mpz_class(static_cast<long>(k) * k) * l0[i];  // - k^2 L~_{k-1}
    trim(h2);
    l0 = std::move(l1);
    l1 = std::move(h2);
  }
  return l1;
}

// 2^n * P_n (Legendre, first kind): coeff of x^{n-2k} = (-1)^k C(2n-2k, n) C(n, k).
inline Poly legendre_poly(int n) {
  Poly p(static_cast<size_t>(n + 1), mpz_class(0));
  for (int k = 0; 2 * k <= n; ++k) {
    mpz_class c = 1;
    // C(2n-2k, n)
    for (int i = 0; i < n; ++i) c *= (2 * n - 2 * k - i);
    for (int i = 2; i <= n; ++i) c /= i;
    // C(n, k)
    mpz_class ck = 1;
    for (int i = 0; i < k; ++i) ck *= (n - i);
    for (int i = 2; i <= k; ++i) ck /= i;
    c *= ck;
    if ((k & 1) != 0) c = -c;
    p[static_cast<size_t>(n - 2 * k)] = c;
  }
  return p;
}

inline Poly wilkinson_like_poly(int n) {
  mpz_class m = n + 1;
  Poly p{1};
  for (int i = 1; i <= n; ++i) p = vmul_poly(p, Poly{-mpz_class(i), m});
  return p;
}

// f = sum a_i x^i, a_i uniform in {-2^tau, ..., 2^tau} (leading forced nonzero); returns f^2 - 1.
inline Poly uniform_clustered_poly(int m, int tau, uint64_t seed) {
  Rng rng(seed);
  const mpz_class span = mpz_class(1) << tau;
  Poly f(static_cast<size_t>(m + 1));
  auto draw = [&]() {
    mpz_class v = uniform_bits(rng, tau + 1);  // uniform in [0, 2^{tau+1})
    v -= span;                                 // shift to [-2^tau, 2^tau)
    if (v == -span || v == span - 1) return mpz_class(0);  // drop extremes: max |c| = 2^tau - 1 (tau bits)
    return v;
  };
  for (int i = 0; i <= m; ++i) f[static_cast<size_t>(i)] = draw();
  while (f.back() == 0) f.back() = draw();
  Poly ff = vmul_poly(f, f);
  ff[0] -= 1;
  return ff;
}

inline Poly mignotte_rat(int n, int tau) {
  const mpz_class a = (mpz_class(1) << ((tau + 1) / 2)) - 1;
  Poly c(static_cast<size_t>(n + 1), mpz_class(0));
  c[0] = -1;
  c[1] = 2 * a;
  c[2] = -a * a;
  c[static_cast<size_t>(n)] = 1;
  return c;
}

// x^n - (a*x^2 - 1)^2 with a = 2^ceil(tau/2) - 1, so max coefficient bits == tau exactly
// (the addendum's irrational-centre caption reads 2^(tau/4)-1, but its bitsize COLUMN reads
// tau/2 of that caption tau, i.e. 2^5-1 at column 10; parameterizing by the column value --
// max bits == tau, same tau-list as the rational family -- reproduces the table exactly).
inline Poly mignotte_irr(int n, int tau) {
  const mpz_class a = (mpz_class(1) << ((tau + 1) / 2)) - 1;
  Poly c(static_cast<size_t>(n + 1), mpz_class(0));
  c[0] = -1;
  c[2] = 2 * a;
  c[4] = -a * a;
  c[static_cast<size_t>(n)] = 1;
  return c;
}

inline Poly dense_uniform(int degree, int tau, uint64_t seed, bool monic, bool trailing_one) {
  Rng rng(seed);
  const mpz_class span = mpz_class(1) << tau;
  Poly c(static_cast<size_t>(degree + 1));
  auto draw = [&]() {
    mpz_class v = uniform_bits(rng, tau + 1);  // uniform in [0, 2^{tau+1})
    v -= span;                                 // shift to [-2^tau, 2^tau)
    if (v == -span || v == span - 1) return mpz_class(0);  // drop extremes: max |c| = 2^tau - 1 (tau bits)
    return v;
  };
  for (int i = 0; i <= degree; ++i) {
    if (monic && i == degree) { c[static_cast<size_t>(i)] = 1; continue; }
    if (trailing_one && i == 0) { c[0] = 1; continue; }
    c[static_cast<size_t>(i)] = draw();
  }
  while (c.back() == 0) c.back() = draw();
  return c;
}

// Res_y(f, g) where f and g are random DENSE BIVARIATE polys of TOTAL degree D
// (deg_y = D, deg_x = D, terms only with i + j <= D), monic in y (y^D coefficient = 1).
// The y^k coefficient is an x-poly of degree <= D - k; this triangle structure makes the
// resultant's x-degree exactly D^2 (the addendum's resultant degree column reads D^2;
// a full bidegree-(D,D) Sylvester would give 2D^2 - D). Coefficients +-(2^bits - 1).
// Returns {resultant, seed actually used}; retries on singular draws (deterministic).
inline std::pair<Poly, uint64_t> res_dense_poly(int D, int bits, uint64_t seed) {
  auto random_total_degree_monic = [&](Rng &rng) {
    std::vector<XPoly> h(static_cast<size_t>(D + 1));
    for (int i = 0; i <= D; ++i) {
      XPoly row(static_cast<size_t>(D - i + 1), mpz_class(0));  // y^i coeff: x-degree <= D - i
      for (int j = 0; j <= D - i; ++j) {
        int64_t mag = 1 + rng.next_below((int64_t(1) << bits) - 1);
        bool neg = (rng.next_u64() & 1) != 0;
        row[static_cast<size_t>(j)] = static_cast<long>(neg ? -mag : mag);
      }
      xp_trim(row);
      h[static_cast<size_t>(i)] = row;
    }
    h.back() = XPoly{1};  // monic in y
    return h;
  };
  for (uint64_t attempt = 0; attempt < 16; ++attempt) {
    uint64_t s = seed + attempt;
    Rng rf(s), rg(s ^ 0x9E3779B97F4A7C15ULL);
    auto f = random_total_degree_monic(rf);
    auto g = random_total_degree_monic(rg);
    auto [res, singular] = resultant_y(f, g, D);
    if (!singular && !res.empty()) return {res, s};
  }
  throw std::runtime_error("res_dense_poly: 16 consecutive singular draws -- something is wrong");
}

}  // namespace bench_families

#endif

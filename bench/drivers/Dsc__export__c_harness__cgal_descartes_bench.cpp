// Single-case CGAL Descartes (bound-free, all-roots) timing, driven by CLI args so
// a shell wrapper can impose a per-case wall-clock kill (macOS has no `timeout`).
// Usage: cgal_descartes_bench dense <degree> <bits> <seed>
//        cgal_descartes_bench mignotte <n> <tau>
#include <boost/multiprecision/gmp.hpp>
#include <gmpxx.h>

#include <chrono>
#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include <CGAL/GMP_arithmetic_kernel.h>
#include <CGAL/Arithmetic_kernel.h>
#include <CGAL/Algebraic_kernel_d/Descartes.h>
#include <CGAL/Polynomial_type_generator.h>

using CGAL_AK = CGAL::GMP_arithmetic_kernel;
using CGAL_Integer = CGAL_AK::Integer;
using CGAL_Rational = CGAL_AK::Rational;
using CGAL_Poly = CGAL::Polynomial_type_generator<CGAL_Integer, 1>::Type;

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

static std::vector<mpz_class> dense_pattern(int degree, int bits, uint64_t seed) {
  std::vector<mpz_class> coeffs(static_cast<size_t>(degree + 1));
  for (int i = 0; i <= degree; ++i) coeffs[static_cast<size_t>(i)] = patterned_coeff(bits, seed, i);
  if (coeffs.back() == 0) coeffs.back() = 1;
  return coeffs;
}

static std::vector<mpz_class> mignotte(int n, int tau) {
  std::vector<mpz_class> c(static_cast<size_t>(n + 1), mpz_class(0));
  mpz_class a = mpz_class(1) << tau;
  c[0] = -2;
  c[1] = 4 * a;
  c[2] = -2 * a * a;
  c[static_cast<size_t>(n)] = 1;
  return c;
}

static CGAL_Poly to_cgal_poly(const std::vector<mpz_class> &coeffs) {
  std::vector<CGAL_Integer> cc;
  cc.reserve(coeffs.size());
  for (const mpz_class &c : coeffs) cc.emplace_back(c.get_mpz_t());
  return CGAL_Poly(cc.begin(), cc.end());
}

static std::vector<mpz_class> parse_coeff_line(const std::string &line) {
  std::vector<mpz_class> coeffs;
  size_t pos = 0;
  while (pos <= line.size()) {
    size_t comma = line.find(',', pos);
    std::string tok = line.substr(pos, comma == std::string::npos ? std::string::npos : comma - pos);
    if (!tok.empty()) coeffs.emplace_back(tok);
    if (comma == std::string::npos) break;
    pos = comma + 1;
  }
  return coeffs;
}

// stdin <name>: read one line of comma-separated decimal coefficients from stdin (lets an
// external driver feed suite_v2_bench.cpp's own generators via its --dump-coeffs mode,
// instead of duplicating every generator into this file -- mirrors the --solve-stdin
// addition in all_roots_vs_competitors_bench.cpp).
static std::vector<mpz_class> read_coeffs_stdin() {
  std::string line;
  if (!std::getline(std::cin, line)) { std::cerr << "stdin: no input line\n"; std::exit(2); }
  std::vector<mpz_class> coeffs = parse_coeff_line(line);
  if (coeffs.empty()) { std::cerr << "stdin: parsed zero coefficients\n"; std::exit(2); }
  return coeffs;
}

int main(int argc, char **argv) {
  std::vector<mpz_class> coeffs;
  std::string name;
  if (argc == 3 && std::string(argv[1]) == "stdin") {
    coeffs = read_coeffs_stdin();
    name = argv[2];
  } else if (argc == 3 && std::string(argv[1]) == "stdin-multi") {
    // SMT-BENCH Phase 2: one poly per line (dump-format "A\t<deg>\t<c0>,...", or bare
    // comma list); sum isolation ms and roots across ALL lines in ONE process. The
    // runner's subprocess cap is the sole supervisor. Emits one per-poly row
    // "P\t<idx>\t<deg>\t<roots>\t<ms>" before the summary line.
    name = argv[2];
    double total_ms = 0.0;
    int64_t total_roots = 0;
    unsigned npolys = 0;
    std::string poly_lines;
    std::string line;
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
      std::vector<mpz_class> cs = parse_coeff_line(coeff_line);
      if (cs.empty()) continue;
      CGAL_Poly f = to_cgal_poly(cs);
      using Isolator = CGAL::internal::Descartes<CGAL_Poly, CGAL_Rational>;
      const auto t0 = std::chrono::steady_clock::now();
      Isolator isolator(f);
      const int n = isolator.number_of_real_roots();
      const auto t1 = std::chrono::steady_clock::now();
      const double ms = std::chrono::duration<double, std::milli>(t1 - t0).count();
      poly_lines += "P\t" + std::to_string(npolys + 1) + "\t" +
                    std::to_string(static_cast<long long>(cs.size()) - 1) + "\t" +
                    std::to_string(n) + "\t" + std::to_string(ms) + "\n";
      total_ms += ms;
      total_roots += n;
      ++npolys;
    }
    if (npolys == 0) { std::cerr << "stdin-multi: no polynomials parsed\n"; return 2; }
    std::cout << poly_lines << name << ",roots=" << total_roots << ",ms=" << total_ms
              << ",polys=" << npolys << "\n";
    std::cout.flush();
    return 0;
  } else if (argc == 5 && std::string(argv[1]) == "dense") {
    int degree = std::atoi(argv[2]), bits = std::atoi(argv[3]);
    uint64_t seed = std::strtoull(argv[4], nullptr, 10);
    coeffs = dense_pattern(degree, bits, seed);
    name = "dense_d" + std::to_string(degree) + "_b" + std::to_string(bits);
  } else if (argc == 4 && std::string(argv[1]) == "mignotte") {
    int n = std::atoi(argv[2]), tau = std::atoi(argv[3]);
    coeffs = mignotte(n, tau);
    name = "mig_n" + std::to_string(n) + "_tau" + std::to_string(tau);
  } else {
    std::cerr << "usage: " << argv[0] << " dense degree bits seed | mignotte n tau\n";
    return 2;
  }

  CGAL_Poly f = to_cgal_poly(coeffs);
  using Isolator = CGAL::internal::Descartes<CGAL_Poly, CGAL_Rational>;

  const auto t0 = std::chrono::steady_clock::now();
  Isolator isolator(f);
  const int n = isolator.number_of_real_roots();
  const auto t1 = std::chrono::steady_clock::now();

  const double ms = std::chrono::duration<double, std::milli>(t1 - t0).count();
  std::cout << name << ",deg=" << (coeffs.size() - 1) << ",roots=" << n << ",ms=" << ms << "\n";
  std::cout.flush();
  return 0;
}

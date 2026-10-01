// libpoly_timer.cpp -- libpoly's real-root isolation, timed on the isolation call only (2026-09-18).
//
// WHY. The campaign harness (all_roots_vs_competitors_bench.cpp:time_libpoly) timed
//     lp_upolynomial_roots_count(f)  +  lp_upolynomial_roots_isolate(f)
// The count exists only to size the output array, yet it is a full squarefree factorisation plus a
// Sturm computation, so libpoly was charged for roughly two solves. Here the array is sized by the
// degree (an upper bound on the number of real roots) OUTSIDE the timed region.
//
// Built twice (same source):
//   libpoly_timer        against the stock libpoly 0.2.1 build   (arm name "libpoly")
//   libpoly_nosqf_timer  against third_party/root_isolators/libpoly_nosqf, whose
//                        upolynomial_roots_isolate_sturm skips the squarefree factorisation
//                        (arm name "libpolysqf"); valid because every input is squarefree.
//
// Interface = all_roots_vs_competitors_bench's:
//   --solve-stdin <name> <solver> [reps]      one polynomial "c0,c1,..." on stdin
//   --solve-stdin-multi <name> <solver>       SMT-BENCH dump lines, summed per instance
//
// Build (LP = the libpoly build dir):
//   clang++ -std=c++20 -O2 -I$LP/../include -I/opt/homebrew/include libpoly_timer.cpp \
//       $LP/src/libpoly.a -L/opt/homebrew/lib -lgmpxx -lgmp -o build/<name>
#include <gmpxx.h>

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

extern "C" {
#include <poly/algebraic_number.h>
#include <poly/integer.h>
#include <poly/upolynomial.h>
}

static std::vector<mpz_class> parse(const std::string &line) {
  std::vector<mpz_class> cs;
  size_t pos = 0;
  while (pos <= line.size()) {
    size_t comma = line.find(',', pos);
    std::string tok = line.substr(pos, comma == std::string::npos ? std::string::npos : comma - pos);
    if (!tok.empty()) cs.emplace_back(tok);
    if (comma == std::string::npos) break;
    pos = comma + 1;
  }
  return cs;
}

static double time_libpoly(const std::vector<mpz_class> &cs, int64_t &count_out) {
  const size_t deg = cs.size() - 1;
  std::vector<lp_integer_t> coeffs(deg + 1);
  for (size_t i = 0; i <= deg; ++i)
    lp_integer_construct_from_string(lp_Z, &coeffs[i], cs[i].get_str().c_str(), 10);
  lp_upolynomial_t *f = lp_upolynomial_construct(lp_Z, deg, coeffs.data());
  for (size_t i = 0; i <= deg; ++i) lp_integer_destruct(&coeffs[i]);
  std::vector<lp_algebraic_number_t> roots(deg > 0 ? deg : 1);  // #real roots <= degree
  size_t roots_size = 0;

  const auto t0 = std::chrono::steady_clock::now();
  lp_upolynomial_roots_isolate(f, roots.data(), &roots_size);
  const auto t1 = std::chrono::steady_clock::now();

  for (size_t i = 0; i < roots_size; ++i) lp_algebraic_number_destruct(&roots[i]);
  lp_upolynomial_delete(f);
  count_out = static_cast<int64_t>(roots_size);
  return std::chrono::duration<double, std::milli>(t1 - t0).count();
}

int main(int argc, char **argv) {
  if (argc < 4) {
    std::cerr << "usage: " << argv[0] << " --solve-stdin|--solve-stdin-multi <name> <solver> [reps]\n";
    return 2;
  }
  const std::string mode = argv[1], name = argv[2], solver = argv[3];
  if (mode == "--solve-stdin") {
    const int reps = argc > 4 ? std::max(1, std::atoi(argv[4])) : 1;
    std::string line;
    if (!std::getline(std::cin, line)) { std::cerr << "no input\n"; return 2; }
    const auto cs = parse(line);
    if (cs.size() < 2) { std::cerr << "need degree >= 1\n"; return 2; }
    double best = 1e30;
    int64_t roots = -1;
    for (int r = 0; r < reps; ++r) {
      int64_t c;
      best = std::min(best, time_libpoly(cs, c));
      roots = c;
    }
    std::cout << name << "," << solver << "_roots=" << roots << "," << solver << "_ms=" << best << "\n";
    return 0;
  }
  if (mode == "--solve-stdin-multi") {
    std::string line, poly_lines;
    double total_ms = 0;
    int64_t total_roots = 0;
    unsigned npolys = 0;
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
      const auto cs = parse(coeff_line);
      if (cs.size() < 2) continue;
      int64_t c = -1;
      const double t = time_libpoly(cs, c);
      poly_lines += "P\t" + std::to_string(npolys + 1) + "\t" + std::to_string(cs.size() - 1) + "\t" +
                    std::to_string(c) + "\t" + std::to_string(t) + "\n";
      total_ms += t;
      total_roots += c;
      ++npolys;
    }
    if (npolys == 0) { std::cerr << "no polynomials parsed\n"; return 2; }
    std::cout << poly_lines << name << "," << solver << "_roots=" << total_roots << "," << solver
              << "_ms=" << total_ms << ",polys=" << npolys << "\n";
    return 0;
  }
  std::cerr << "unknown mode " << mode << "\n";
  return 2;
}

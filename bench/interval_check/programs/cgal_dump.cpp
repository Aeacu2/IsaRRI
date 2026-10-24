// cgal_dump.cpp -- the isolating intervals of the CGAL arm (CGAL::internal::Descartes, the isolator
// cgal_descartes_bench times), for the interval check (docs/LOGCF_PLAN_2026-10-08.md section 8). NOT a
// timing tool. stdout: "I\t<name>\t<idx>\t<left>\t<right>" per root (left = right when is_exact_root),
// "E\t<name>\t<idx>" after each polynomial. Usage: cgal_dump stdin|stdin-multi <name>
// Build: clang++ -std=c++17 -O2 -I/opt/homebrew/include cgal_dump.cpp -L/opt/homebrew/lib -lgmpxx -lgmp -lmpfr
#include <boost/multiprecision/gmp.hpp>
#include <gmpxx.h>
#include <iostream>
#include <sstream>
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
static std::string q(const CGAL_Rational &r) { std::ostringstream o; o << r; return o.str(); }
int main(int argc, char **argv) {
  if (argc != 3) return 2;
  const bool multi = std::string(argv[1]) == "stdin-multi";
  const std::string name = argv[2];
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
    std::vector<CGAL_Integer> cc;
    size_t pos = 0;
    while (pos <= cl.size()) {
      size_t comma = cl.find(',', pos);
      std::string tok = cl.substr(pos, comma == std::string::npos ? std::string::npos : comma - pos);
      if (!tok.empty()) cc.emplace_back(mpz_class(tok).get_mpz_t());
      if (comma == std::string::npos) break;
      pos = comma + 1;
    }
    if (!cc.empty()) {
      CGAL_Poly f(cc.begin(), cc.end());
      CGAL::internal::Descartes<CGAL_Poly, CGAL_Rational> iso(f);
      const int n = iso.number_of_real_roots();
      for (int i = 0; i < n; ++i)
        std::cout << "I\t" << name << "\t" << idx << "\t" << q(iso.left_bound(i)) << "\t"
                  << q(iso.is_exact_root(i) ? iso.left_bound(i) : iso.right_bound(i)) << "\n";
      std::cout << "E\t" << name << "\t" << idx << "\n";
    }
    if (!multi) break;
  }
  return 0;
}

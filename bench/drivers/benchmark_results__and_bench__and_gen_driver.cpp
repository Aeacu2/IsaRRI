// and_gen_driver.cpp — AND_BENCH coefficient generator for the rows NOT covered by suite reuse.
//
// Reuses the frozen suite generator header (Dsc/export/c_harness/bench_families.hpp — pure
// math, decoupled from any solver header) so every construction is byte-identical to the one
// the 135-case record run used for the same families. This file is NEW (the frozen files are
// untouched; the freeze manifest pins them by sha).
//
// Usage:
//   g++ -O2 -std=c++17 -I Dsc/export/c_harness -I "$(brew --prefix gmp)/include" \
//       and_gen_driver.cpp -L"$(brew --prefix gmp)/lib" -lgmpxx -lgmp -o /tmp/and_gen_driver
//   /tmp/and_gen_driver <gen_list.txt> <out_dir>
//
// gen_list.txt lines (produced by and_gen.py):  name<TAB>ctor<TAB>a<TAB>b<TAB>c<TAB>seed
//   ctor    meaning (all arguments per bench_families.hpp):
//   nested_mignotte  nested_mignotte_poly(a=n, b=tau)     tau % 8 == 0 enforced
//   mignotte_rat     mignotte_rat(a=n, b=tau)             tau even; max bits == tau
//   mignotte_irr     mignotte_irr(a=n, b=tau)             tau even; max bits == tau
//   chebyshev_t/u    chebyshev_poly(a=n) / chebyshev_u_poly(a=n)
//   hermite          hermite_poly(a=n)                   physicists' H_n
//   laguerre         laguerre_poly(a=n)                  n! * L_n (page-exact bitsize)
//   legendre         legendre_poly(a=n)                  2^n * P_n
//   wilkinson        wilkinson_poly(a=n)
//   wilkinson_like   wilkinson_like_poly(a=n)            prod((n+1)x - i)
//   gauss_sqrtn      gaussian_clustered_poly(a=m, b=512, seed)   degree 2m
//   gauss_logn       uniform_clustered_poly(a=m, b=512, seed)    degree 2m
//   dense            dense_uniform(a=d, b=1024, seed, c in {0 plain,1 monic,2 monic+t1})
//   resultant        res_dense_poly(a=D, b=10, seed).first        degree D^2
//
// Output: <out_dir>/<name>.txt — constant-first comma-separated coefficients (a0,a1,...,an),
// the harness --solve-stdin convention, identical to the suite's coeffs/ files.

#include "bench_families.hpp"
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>

using namespace bench_families;

static void write_poly(const std::string &path, const Poly &p) {
  std::ofstream out(path.c_str());
  if (!out) { std::cerr << "cannot write " << path << "\n"; std::exit(1); }
  for (size_t i = 0; i < p.size(); ++i) {
    if (i) out << ",";
    out << p[i];
  }
  out << "\n";
}

static Poly dispatch(const std::string &ctor, long long a, long long b, long long c,
                     unsigned long long seed) {
  if (ctor == "nested_mignotte") return nested_mignotte_poly((int)a, (int)b);
  if (ctor == "mignotte_rat")    return mignotte_rat((int)a, (int)b);
  if (ctor == "mignotte_irr")    return mignotte_irr((int)a, (int)b);
  if (ctor == "chebyshev_t")     return chebyshev_poly((int)a);
  if (ctor == "chebyshev_u")     return chebyshev_u_poly((int)a);
  if (ctor == "hermite")         return hermite_poly((int)a);
  if (ctor == "laguerre")        return laguerre_poly((int)a);
  if (ctor == "legendre")        return legendre_poly((int)a);
  if (ctor == "wilkinson")       return wilkinson_poly((int)a);
  if (ctor == "wilkinson_like")  return wilkinson_like_poly((int)a);
  if (ctor == "gauss_sqrtn")     return gaussian_clustered_poly((int)a, (int)b, seed);
  if (ctor == "gauss_logn")      return uniform_clustered_poly((int)a, (int)b, seed);
  if (ctor == "dense") {
    bool monic = (c == 1), t1 = (c == 2);
    return dense_uniform((int)a, (int)b, seed, monic, t1);
  }
  if (ctor == "resultant")       return res_dense_poly((int)a, (int)b, seed).first;
  std::cerr << "unknown constructor: " << ctor << "\n";
  std::exit(1);
}

int main(int argc, char **argv) {
  if (argc != 3) {
    std::cerr << "usage: and_gen_driver <gen_list.txt> <out_dir>\n";
    return 1;
  }
  std::ifstream in(argv[1]);
  if (!in) { std::cerr << "cannot open " << argv[1] << "\n"; return 1; }
  std::string line;
  int done = 0;
  while (std::getline(in, line)) {
    if (line.empty() || line[0] == '#') continue;
    std::istringstream ss(line);
    std::string name, ctor;
    long long a, b, c;
    unsigned long long seed;
    if (!(ss >> name >> ctor >> a >> b >> c >> seed)) {
      std::cerr << "bad line: " << line << "\n";
      return 1;
    }
    Poly p = dispatch(ctor, a, b, c, seed);
    write_poly(std::string(argv[2]) + "/" + name + ".txt", p);
    ++done;
  }
  std::cout << "wrote " << done << " polynomials to " << argv[2] << "\n";
  return 0;
}

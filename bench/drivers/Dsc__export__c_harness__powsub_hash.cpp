// powsub_hash.cpp -- T-e instrument for the thesis campaign
// (docs/THESIS_CAMPAIGN_PLAN.md §4 bar T-e: interval-hash identity).
//
// Calls `all_dsc_powsub_main` (same knobs as the campaign: nfloor=22, hcap=32,
// dlt=8) over polynomials read from stdin and prints a canonical hash of the
// EMITTED WINDOWS -- not root counts -- per polynomial:
//
//   H\t<idx>\t<roots>\t<hash16>
//
// plus a summary line "<name>,hash_roots=<R>,hash_polys=<N>".
//
// The hash is FNV-1a-64 over, in order: pos_count, neg_count, xs0, then per
// positive window (lnum, rnum as canonical decimal, k as 8 LE bytes) in index
// order, then per negative window likewise. Field tags separate domains so no
// two distinct window lists collide by concatenation.
//
// Input: one polynomial per line -- either a bare comma list "c0,c1,...,cn"
// (MPSolve/AND coeffs files) or nlsat dump-format "A\t<deg>\t<c0>,..." (SMT
// .apolys files, possibly many polys per invocation). Lines that are empty or
// non-A-tabbed are skipped, mirroring suite_v2_bench.cpp's --solve-stdin-multi.
//
// This is a COUNT, not a timing: no clock is read and no ms is printed, so the
// output is load-insensitive. A crash/hang kills the process (the caller's
// subprocess cap is the supervisor); a negative count line marks corruption.
//
// Build (mirrors scripts/build-allcomp-bench.sh, no fast-path objects):
//   clang++ -std=c++17 -O2 -w -DDSC_ENTRIES_PUBLIC -I"$GMP/include" \
//     powsub_hash.cpp <artifact.ll> lib_isabelle_llvm_<label>.o \
//     -L"$GMP/lib" -lgmpxx -lgmp -o build/powsub_hash_<label>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <gmpxx.h>
#include <iostream>
#include <string>
#include <vector>

extern "C" {
#include "../dsc_adaptive.h"
}

static gmp_mpz_struct *as_gmp_ptr(mpz_class &x) {
  return reinterpret_cast<gmp_mpz_struct *>(x.get_mpz_t());
}
static gmp_mpz_struct *as_gmp_ptr_const(const mpz_class &x) {
  return reinterpret_cast<gmp_mpz_struct *>(const_cast<__mpz_struct *>(x.get_mpz_t()));
}

// ---- FNV-1a-64 -------------------------------------------------------------
struct Fnv {
  uint64_t h = 14695981039346656037ULL;
  void bytes(const void *p, size_t n) {
    const unsigned char *b = static_cast<const unsigned char *>(p);
    for (size_t i = 0; i < n; ++i) {
      h ^= b[i];
      h *= 1099511628211ULL;
    }
  }
  void tag(char c) { bytes(&c, 1); }
  void i64(int64_t v) {
    unsigned char b[8];
    for (int i = 0; i < 8; ++i) b[i] = static_cast<unsigned char>((v >> (8 * i)) & 0xFF);
    bytes(b, 8);
  }
  void mpz(const mpz_class &x) {
    // Canonical decimal; sign included by mpz_get_str. Length-prefix so
    // ("12","3") and ("1","23") hash differently even across a tag failure.
    char *s = mpz_get_str(nullptr, 10, x.get_mpz_t());
    size_t n = strlen(s);
    i64(static_cast<int64_t>(n));
    bytes(s, n);
    void (*freefunc)(void *, size_t);
    mp_get_memory_functions(nullptr, nullptr, &freefunc);
    freefunc(s, n + 1);
  }
};

static void solve_one(const std::vector<mpz_class> &coeffs, Fnv &f, int64_t &roots) {
  std::vector<mpz_class> c = coeffs;
  while (c.size() > 1 && c.back() == 0) c.pop_back();
  const int64_t n = static_cast<int64_t>(c.size());
  std::vector<gmp_mpz_struct *> ptrs;
  ptrs.reserve(c.size());
  for (const mpz_class &x : c) ptrs.push_back(as_gmp_ptr_const(x));

  std::vector<mpz_class> pos_l(n), pos_r(n), neg_l(n), neg_r(n);
  std::vector<gmp_mpz_struct *> pos_lp, pos_rp, neg_lp, neg_rp;
  std::vector<int64_t> pos_k(n, -1), neg_k(n, -1);
  for (int64_t i = 0; i < n; ++i) {
    pos_lp.push_back(as_gmp_ptr(pos_l[i]));
    pos_rp.push_back(as_gmp_ptr(pos_r[i]));
    neg_lp.push_back(as_gmp_ptr(neg_l[i]));
    neg_rp.push_back(as_gmp_ptr(neg_r[i]));
  }
  int64_t pos_count = -1, neg_count = -1, xs0 = -1, out_ok = 0;
  all_dsc_powsub_main(&pos_count, pos_lp.data(), pos_rp.data(), pos_k.data(),
                      &neg_count, neg_lp.data(), neg_rp.data(), neg_k.data(),
                      &xs0, &out_ok, n,
                      /*nfloor=*/22, /*hcap=*/32, /*dlt=*/8, n, ptrs.data());
  if (pos_count < 0 || pos_count > n || neg_count < 0 || neg_count > n) {
    roots = -1;
    return;
  }
  roots = pos_count + neg_count + (xs0 == 1 ? 1 : 0);
  f.tag('P');
  f.i64(pos_count);
  f.tag('N');
  f.i64(neg_count);
  f.tag('Z');
  f.i64(xs0);
  for (int64_t i = 0; i < pos_count; ++i) {
    f.tag('l');
    f.mpz(pos_l[i]);
    f.tag('r');
    f.mpz(pos_r[i]);
    f.tag('k');
    f.i64(pos_k[i]);
  }
  for (int64_t i = 0; i < neg_count; ++i) {
    f.tag('l');
    f.mpz(neg_l[i]);
    f.tag('r');
    f.mpz(neg_r[i]);
    f.tag('k');
    f.i64(neg_k[i]);
  }
}

static bool parse_coeffs(const std::string &s, std::vector<mpz_class> &out) {
  out.clear();
  size_t pos = 0;
  while (pos <= s.size()) {
    size_t comma = s.find(',', pos);
    std::string tok =
        s.substr(pos, comma == std::string::npos ? std::string::npos : comma - pos);
    if (!tok.empty()) {
      try {
        out.emplace_back(tok);
      } catch (...) {
        return false;
      }
    }
    if (comma == std::string::npos) break;
    pos = comma + 1;
  }
  return !out.empty();
}

int main(int argc, char **argv) {
  if (argc < 2) {
    std::cerr << "usage: powsub_hash <name> < poly_lines\n";
    return 2;
  }
  const std::string name = argv[1];
  std::string line;
  int64_t idx = 0, total_roots = 0;
  while (std::getline(std::cin, line)) {
    if (line.empty()) continue;
    std::string coeff_line = line;
    size_t tab = line.find('\t');
    if (tab != std::string::npos) {
      if (line.compare(0, 1, "A") != 0) continue;  // B line or malformed -- skip
      size_t tab2 = line.find('\t', tab + 1);
      if (tab2 == std::string::npos) continue;
      coeff_line = line.substr(tab2 + 1);
    }
    std::vector<mpz_class> coeffs;
    if (!parse_coeffs(coeff_line, coeffs)) {
      std::cout << "H\t" << (idx + 1) << "\t-1\tCORRUPT\n";
      std::cout.flush();
      return 0;
    }
    Fnv f;
    int64_t roots = -1;
    solve_one(coeffs, f, roots);
    if (roots < 0) {
      std::cout << "H\t" << (idx + 1) << "\t-1\tCORRUPT\n";
      std::cout.flush();
      return 0;
    }
    ++idx;
    total_roots += roots;
    char hex[17];
    snprintf(hex, sizeof hex, "%016llx", (unsigned long long)f.h);
    std::cout << "H\t" << idx << "\t" << roots << "\t" << hex << "\n";
  }
  if (idx == 0) {
    std::cerr << "powsub_hash: no polynomials parsed\n";
    return 2;
  }
  std::cout << name << ",hash_roots=" << total_roots << ",hash_polys=" << idx << "\n";
  std::cout.flush();
  return 0;
}

// z3_isolate_timer.cpp -- time z3's all-roots Descartes isolation (Path A) standalone.
//
// The SMT-BENCH track races our solver against what z3's NLSAT engine actually calls when it
// isolates: `upolynomial::manager::sqf_isolate_roots` (algebraic_numbers.cpp:640, Path A).
// This driver links z3's internal polynomial machinery from the vendored, already-built tree
// and times that exact function on polynomials extracted by the nlsat_polydump hook
// (docs/SMT_BENCH.md §3, §5.2).
//
// Input: dump-format lines on stdin or as file arguments --
//     <A|B>\t<degree>\t<c0>,<c1>,...,<cd>      (coefficients LOW-DEGREE-FIRST decimals)
// Output per timed polynomial (TSV):
//     <path>\t<degree>\t<nroots>\t<ns>
//
// Path A never emits degree-1 or degree-0 polynomials (solved upstream), and the race is
// Path A only; B lines are skipped unless --include-b is given (and even then, timing B via
// sqf_isolate_roots is NOT the two-root Sturm query z3 actually performs for B -- that would
// be isolate_roots_closest_univariate; do not quote B timings from this driver).
//
// Build (macOS, against the existing vendored build -- does NOT rebuild z3; the flags must
// match build/config.mk: -std=c++20 and -D_MP_INTERNAL for the internal bignums):
//   clang++ -std=c++20 -O2 -D_MP_INTERNAL -I third_party/z3_snapshot_20260612/src \
//       benchmark_results/smt_bench/z3_isolate_timer.cpp \
//       third_party/z3_snapshot_20260612/build/libz3.a -o z3_isolate_timer
//
// Verify after building: the binary must resolve upolynomial symbols from libz3.a (static
// link) and produce sane isolating-interval counts on the smoke corpus (scripts in §5.2's
// two-phase protocol; the per-line flush of the dump hook is OUT of this loop).

#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#include "math/polynomial/upolynomial.h"
#include "util/mpbq.h"
#include "util/rlimit.h"

namespace {

struct PolyRow {
    char path;         // 'A' or 'B' from the dump line; ' ' when bare coefficients
    unsigned degree;
    std::vector<std::string> coeffs;   // low-degree-first
};

// Parse one dump-format line. Returns false for empty/invalid lines (skipped, not fatal).
bool parse_line(const std::string & line, PolyRow & out) {
    if (line.empty() || line[0] == '\n' || line[0] == '\r')
        return false;

    // Optional leading path tag: "<A|B>\t..."
    const char * p = line.c_str();
    if ((*p == 'A' || *p == 'B') && p[1] == '\t') {
        out.path = *p;
        p += 2;
    } else {
        out.path = ' ';
    }

    // "<degree>\t<c0>,<c1>,..."
    char * end = nullptr;
    long deg = strtol(p, &end, 10);
    if (end == p || *end != '\t')
        return false;
    if (deg < 0)
        return false;
    out.degree = static_cast<unsigned>(deg);

    const char * cs = end + 1;
    out.coeffs.clear();
    std::string cur;
    for (const char * q = cs; *q != '\0' && *q != '\n' && *q != '\r'; ++q) {
        if (*q == ',') {
            out.coeffs.push_back(cur);
            cur.clear();
        } else {
            cur.push_back(*q);
        }
    }
    if (!cur.empty())
        out.coeffs.push_back(cur);

    // degree + 1 coefficients are expected (low-degree-first, inclusive).
    return out.coeffs.size() == static_cast<size_t>(deg) + 1;
}

// --sum mode state (Phase 2: one driver invocation per (instance, arm, rep); the runner's
// subprocess cap is the sole supervisor). Accumulated across all polynomials of the file.
// When emit_poly is on, each timed poly ALSO prints one per-poly row
// "P\t<idx>\t<deg>\t<nroots>\t<ns>" (1-based idx in input order; ns, not ms -- the runner
// converts), before the final totals line. The warmup run must never print one of these.
long sum_ns = 0;
unsigned sum_roots = 0;
unsigned sum_npolys = 0;
bool sum_mode = false;
bool emit_poly = false;
unsigned sum_idx = 0;

void run(upolynomial::manager & upm, mpbq_manager & bqm,
         const PolyRow & row, bool verbose) {
    // A never emits constants/linears; guard anyway (nothing to isolate).
    if (row.coeffs.size() < 3) {
        if (sum_mode) { ++sum_npolys; return; }
        std::printf("%c\t%u\t-\t-\n", row.path, row.degree);
        return;
    }

    upolynomial::numeral_vector f;
    for (const auto & c : row.coeffs) {
        f.push_back(mpz());
        upm.zm().set(f.back(), c.c_str());
    }

    mpbq_vector roots, lowers, uppers;
    auto t0 = std::chrono::steady_clock::now();
    upm.sqf_isolate_roots(f.size(), f.data(), bqm, roots, lowers, uppers);
    auto t1 = std::chrono::steady_clock::now();

    // Rational roots land in `roots` (exact mpbq); irrational roots land as isolating
    // intervals in `lowers`/`uppers`. Total distinct real roots = roots.size() + lowers.size().
    if (lowers.size() != uppers.size()) {
        std::fprintf(stderr, "z3_isolate_timer: inconsistent intervals (%u rational, %u/%u interval bounds) -- bug in driver, not z3\n",
                     static_cast<unsigned>(roots.size()), static_cast<unsigned>(lowers.size()), static_cast<unsigned>(uppers.size()));
        std::exit(2);
    }
    unsigned nroots = static_cast<unsigned>(roots.size() + lowers.size());

    long ns = std::chrono::duration_cast<std::chrono::nanoseconds>(t1 - t0).count();
    if (sum_mode) {
        sum_ns += ns;
        sum_roots += nroots;
        sum_npolys += 1;
        if (emit_poly) {
            std::printf("P\t%u\t%u\t%u\t%ld\n", sum_idx + 1, row.degree, nroots, ns);
            ++sum_idx;
        }
        return;
    }
    std::printf("%c\t%u\t%u\t%ld\n", row.path, row.degree, nroots, ns);

    for (auto & x : f)
        upm.zm().del(x);
    bqm.reset(roots);
    bqm.reset(lowers);
    bqm.reset(uppers);
}

}  // namespace

int main(int argc, char ** argv) {
    bool include_b = false;
    bool verbose = false;
    std::vector<std::string> files;
    for (int i = 1; i < argc; ++i) {
        if (std::strcmp(argv[i], "--include-b") == 0)
            include_b = true;
        else if (std::strcmp(argv[i], "--verbose") == 0)
            verbose = true;
        else if (std::strcmp(argv[i], "--sum") == 0)
            sum_mode = true;
        else
            files.push_back(argv[i]);
    }

    reslimit lim;
    unsynch_mpz_manager zm;
    upolynomial::manager upm(lim, zm);
    mpbq_manager bqm(zm);

    // Warmup: one isolation so page faults / allocator warmup land outside the measurements.
    {
        PolyRow warm;
        warm.path = 'W';
        warm.degree = 2;
        warm.coeffs = {"-2", "0", "1"};   // x^2 - 2
        run(upm, bqm, warm, verbose);
    }
    // The warmup row above must never count toward --sum totals.
    sum_ns = 0;
    sum_roots = 0;
    sum_npolys = 0;
    emit_poly = true;

    auto process = [&](const std::string & path) {
        std::FILE * f = path == "-" ? stdin : std::fopen(path.c_str(), "r");
        if (!f) {
            std::fprintf(stderr, "z3_isolate_timer: cannot open %s\n", path.c_str());
            std::exit(1);
        }
        char buf[1 << 16];
        std::string line;
        unsigned n = 0;
        while (std::fgets(buf, sizeof(buf), f)) {
            line = buf;
            while (!line.empty() && (line.back() == '\n' || line.back() == '\r'))
                line.pop_back();
            PolyRow row;
            if (!parse_line(line, row))
                continue;
            if (row.path == 'B' && !include_b)
                continue;
            run(upm, bqm, row, verbose);
            ++n;
        }
        if (f != stdin)
            std::fclose(f);
        if (verbose)
            std::fprintf(stderr, "z3_isolate_timer: %s: %u polynomials timed\n", path.c_str(), n);
    };

    if (files.empty())
        files.push_back("-");
    for (const auto & f : files)
        process(f);

    if (sum_mode) {
        // Single totals line: <total_roots>\t<total_ns>\t<npolys> -- the Phase 2 row shape
        // (oracle = z3's summed nroots per instance; arm timing = summed ns).
        std::printf("%u\t%ld\t%u\n", sum_roots, sum_ns, sum_npolys);
        std::fflush(stdout);
    }
    return 0;
}

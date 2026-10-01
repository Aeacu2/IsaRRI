#!/usr/bin/env python3
"""AND_BENCH generation orchestrator: map the 295-point ANewDsc grid (manifest.tsv) to
concrete constructions, reusing the frozen 135-case suite's instances where they ARE the
page's rows, and emitting a generation spec for the rest.

Run from the repo root:  python3 benchmark_results/and_bench/and_gen.py [--materialize]

Design (docs/AND_BENCH.md §2/§3):
  - Every page family maps to a constructor in Dsc/export/c_harness/bench_families.hpp (the
    frozen suite generator header, included by and_gen_driver.cpp) — the suite's constructors
    are the page's constructions (verified: laguerre bitsize matches the page column exactly,
    743/1723/3933 at d128/256/512; wilkinson exact; nested/mignotte/gauss/dense within +-2).
  - REUSE: 90 suite instances are byte-identical page rows (same family, same degree, same
    construction, verified against the suite's coeffs/ on disk). Their coeffs files are copied
    verbatim (--materialize) — cross-track continuity with the 135-case record run.
  - GENERATE: the remaining ~205 rows, via and_gen_driver.cpp (compiled from the frozen header;
    build/run is the deferred CPU phase).

Outputs (all under benchmark_results/and_bench/):
  gen_spec.tsv        one row per case: name family table degree bits_target constructor a b
                      seed source suite_case oracle achieved_bits
  gen_list.txt        GENERATE rows for and_gen_driver.cpp: name<TAB>ctor<TAB>a<TAB>b<TAB>seed
  cases_record.json   the final-suite-run.py table ({id,band,family,degree,desc,oracle,name});
                      oracle = analytic where a theorem, else 'PENDING' for the oracle phase
  coeffs/<name>.txt   materialized REUSE copies (only with --materialize)

Seeds (pre-registered): REUSE rows keep the suite's seed (irrelevant — the file is copied);
GENERATE rows of the seeded families (gauss_*, random_*, resultant): seed = 20260808
+ 100*f_index + r, f_index = order in the family table below, r = 0-based manifest order.
"""
import json
import math
import os
import sys

sys.set_int_max_str_digits(0)  # suite coeffs reach 2^65536 (~20k digits); the 4300-digit default bites

HERE = os.path.dirname(os.path.abspath(__file__))
MANIFEST = os.path.join(HERE, "manifest.tsv")
SUITE_COEFFS = "benchmark_results/final_suite/coeffs"
OUT_DIR = HERE
COEFFS_DIR = os.path.join(HERE, "coeffs")

# ---- the page's 16 families, in the docs/AND_BENCH.md §2 table order (f_index = order) ----
FAMILIES = [
    "nested_mignotte", "mignotte_rat", "mignotte_irr", "gauss_sqrtn", "gauss_logn",
    "random_dense", "random_monic", "random_monic_lt1", "resultant",
    "chebyshev_T", "chebyshev_U", "hermite", "laguerre", "legendre",
    "wilkinson", "wilkinson_like",
]

# Bit-length semantics of the page's bitsize column per family (measured, docs §3):
#   EXACT    page column == natural max-coeff bit-length (within +-2) — G1 gate applies
#   TWOFOLD  page column ~= 2x natural (its convention; suite-documented) — recorded, no gate
#   WILKLIKE page column ~= 0.92-0.95x natural (construction differs from prod((n+1)x-i)) — recorded
#   RESULT   page column >> natural (its f,g coefficient magnitude is unspecified) — recorded
BITS_CLASS = {
    "nested_mignotte": "EXACT", "mignotte_rat": "EXACT", "mignotte_irr": "EXACT",
    "gauss_sqrtn": "EXACT", "gauss_logn": "EXACT",
    "random_dense": "EXACT", "random_monic": "EXACT", "random_monic_lt1": "EXACT",
    "laguerre": "EXACT", "wilkinson": "EXACT",
    "chebyshev_T": "TWOFOLD", "chebyshev_U": "TWOFOLD", "hermite": "TWOFOLD",
    "legendre": "TWOFOLD", "wilkinson_like": "WILKLIKE", "resultant": "RESULT",
}

# ---- suite reuse: (and_family, table, degree, bitsize) -> (suite case id, suite file base) ----
# Derived from the frozen Dsc/export/c_harness/final_suite_cases.hpp dispatch (140 cases),
# validated against the suite's coeffs on disk (docs/AND_BENCH.md §3): the suite's constructors
# at these (degree, parameter) points reproduce the page's rows byte-for-byte.
# nested (ids 1-5): page t02 rows at bitsize 140 (tau=56); nestedTau (126-130): page t01 rows,
#   tau=8*round(b/20): 16->38, 256->640, 1024->2560, 4096->10240, 11584->28960 (all measured).
SUITE = []
def _r(fam, table, deg, bits, case):
    SUITE.append((fam, table, deg, bits, case, f"case_{case}_{{}}.txt"))
# nested_mignotte: t01 (d260 tau-sweep) / t02 (n-sweep b140)
for case, tau, b in [(126, 16, 38), (127, 256, 640), (128, 1024, 2560),
                     (129, 4096, 10240), (130, 11584, 28960)]:
    _r("nested_mignotte", 1, 260, b, case)
for case, d in [(1, 132), (2, 260), (3, 1028), (4, 2900), (5, 5796)]:
    _r("nested_mignotte", 2, d, 140, case)
# mignotte_rat: t10 (d129 tau-sweep) / t11 (b14 degree-sweep)
for case, tau in [(41, 10), (42, 512), (43, 2048), (44, 16384), (45, 65536)]:
    _r("mignotte_rat", 10, 129, tau, case)
for case, d in [(131, 513), (132, 1449), (133, 2897), (134, 5793), (135, 16385)]:
    _r("mignotte_rat", 11, d, 14, case)
# mignotte_irr: t12 / t13
for case, tau in [(46, 10), (47, 512), (48, 2048), (49, 16384), (50, 65536)]:
    _r("mignotte_irr", 12, 129, tau, case)
for case, d in [(136, 363), (137, 725), (138, 1449), (139, 2897), (140, 8193)]:
    _r("mignotte_irr", 13, d, 14, case)
# chebyshev T/U, hermite, laguerre, legendre: page degrees {128,256,512,1024,2048}
for fam, t, cases in [("chebyshev_T", 3, range(6, 11)), ("chebyshev_U", 4, range(11, 16)),
                      ("hermite", 7, range(16, 21)), ("laguerre", 8, range(21, 26)),
                      ("legendre", 9, range(26, 31))]:
    for case, d in zip(cases, [128, 256, 512, 1024, 2048]):
        _r(fam, t, d, None, case)
# gauss_sqrtn: d in {32,1024,2048} (suite m=16,512,1024; its d360/7280 are not page rows)
for case, d in [(31, 32), (33, 1024), (34, 2048)]:
    _r("gauss_sqrtn", 5, d, None, case)
# gauss_logn: d in {64,1024,4096,8192,16384}
for case, d in [(36, 64), (37, 1024), (38, 4096), (39, 8192), (40, 16384)]:
    _r("gauss_logn", 6, d, None, case)
# random dense families: d in {128,512,2048,8192,16384}, tau=1024
for fam, t, cases in [("random_dense", 15, range(56, 61)), ("random_monic", 16, range(61, 66)),
                      ("random_monic_lt1", 17, range(66, 71))]:
    for case, d in zip(cases, [128, 512, 2048, 8192, 16384]):
        _r(fam, t, d, 1024, case)
# resultant: D in {12,24,32,40} -> d in {144,576,1024,1600} (D=48 -> d2304 not a page row)
for case, D in [(51, 12), (52, 24), (53, 32), (54, 40)]:
    _r("resultant", 14, D * D, None, case)
# wilkinson / wilkinson_like: page degrees (wilkinson max 2048; wilkinLike 4096 not a page row)
for case, d in [(76, 128), (77, 256), (78, 512), (79, 1024)]:
    _r("wilkinson", 19, d, None, case)
for case, d in [(71, 128), (72, 256), (73, 1024), (74, 2048)]:
    _r("wilkinson_like", 18, d, None, case)
SUITE_LOOKUP = {(fam, table, deg, bits): case for fam, table, deg, bits, case, _ in SUITE}

# ---- constructor dispatch (mirrors final_suite_cases.hpp generate(); and_gen_driver.cpp) ----
def ctor_for(family, table, degree, bits):
    """Return (constructor, a, b, c) for the C++ driver; None if the row is REUSE."""
    if family == "nested_mignotte":
        return ("nested_mignotte", degree, 8 * round(bits / 20) if table == 1 else 56, 0)
    if family == "mignotte_rat":
        return ("mignotte_rat", 129 if table == 10 else degree,
                14 if table == 11 else bits, 0)
    if family == "mignotte_irr":
        return ("mignotte_irr", 129 if table == 12 else degree,
                14 if table == 13 else bits, 0)
    if family == "chebyshev_T": return ("chebyshev_t", degree, 0, 0)
    if family == "chebyshev_U": return ("chebyshev_u", degree, 0, 0)
    if family == "hermite": return ("hermite", degree, 0, 0)
    if family == "laguerre": return ("laguerre", degree, 0, 0)
    if family == "legendre": return ("legendre", degree, 0, 0)
    if family == "gauss_sqrtn": return ("gauss_sqrtn", degree // 2, 512, 0)
    if family == "gauss_logn": return ("gauss_logn", degree // 2, 512, 0)
    if family == "random_dense": return ("dense", degree, 1024, 0)
    if family == "random_monic": return ("dense", degree, 1024, 1)
    if family == "random_monic_lt1": return ("dense", degree, 1024, 2)
    if family == "resultant": return ("resultant", int(math.isqrt(degree)), 10, 0)
    if family == "wilkinson": return ("wilkinson", degree, 0, 0)
    if family == "wilkinson_like": return ("wilkinson_like", degree, 0, 0)
    raise ValueError(family)


def suite_file_family(family, table):
    """Suite coeffs family-name suffix (final_suite_cases.hpp kCases names)."""
    return {"chebyshev_T": "chebyshevT", "chebyshev_U": "chebyshevU",
            "mignotte_rat": "migRat" if table == 10 else "migRatDeg",
            "mignotte_irr": "migIrr" if table == 12 else "migIrrDeg",
            "random_dense": "dense", "random_monic": "denseMon",
            "random_monic_lt1": "denseM1", "wilkinson_like": "wilkinLike",
            "nested_mignotte": "nested" if table == 2 else "nestedTau",
            "gauss_sqrtn": "gaussSqrt", "gauss_logn": "gaussLogN",
            "resultant": "resultant", "hermite": "hermite", "laguerre": "laguerre",
            "legendre": "legendre", "wilkinson": "wilkinson"}[family]


def analytic_oracle(family, degree):
    """Oracle where a theorem (else None -> PENDING for the oracle phase)."""
    if family in ("chebyshev_T", "chebyshev_U", "hermite", "laguerre", "legendre",
                  "wilkinson", "wilkinson_like"):
        return degree                      # exactly n distinct real roots
    if family in ("mignotte_rat", "mignotte_irr") and degree % 2 == 1:
        return 3                            # parity argument, suite-verified (frozen oracle)
    return None


def bits_of(path):
    txt = open(path).read().strip().strip("[]")
    cs = [int(x) for x in txt.split(",") if x.strip() != ""]
    return len(cs) - 1, max(c.bit_length() for c in cs)


def main():
    rows = []
    for line in open(MANIFEST):
        if line.startswith("#") or not line.strip():
            continue
        p = line.rstrip("\n").split("\t")
        rows.append((p[0], int(p[1]), p[2], int(p[3]), int(p[4]), p[5]))

    spec, glist, records, stats = [], [], [], {"reuse": 0, "gen": 0}
    by_fam_r = {}
    for name, table, family, degree, bits, anew in rows:
        by_fam_r[family] = by_fam_r.get(family, 0) + 1
        r = by_fam_r[family] - 1
        f_idx = FAMILIES.index(family)
        seed = 20260808 + 100 * f_idx + r
        suite_case = SUITE_LOOKUP.get((family, table, degree, bits)) or \
                     SUITE_LOOKUP.get((family, table, degree, None))
        source = "reuse" if suite_case else "gen"
        achieved = ""
        if suite_case:
            # find the suite's disk file (family-name suffix per final_suite_cases.hpp)
            fam_suite = suite_file_family(family, table)
            # table 1 nested rows come from suite family nestedTau, table 2 from nested
            path = os.path.join(SUITE_COEFFS, f"case_{suite_case}_{fam_suite}.txt")
            if not os.path.exists(path):
                sys.exit(f"FATAL: suite file missing: {path}")
            d, b = bits_of(path)
            assert d == degree, f"suite file {path}: degree {d} != page {degree}"
            achieved = b
        ctor, a, b, c = ctor_for(family, table, degree, bits)
        ora = analytic_oracle(family, degree)
        # REUSE rows inherit the suite's frozen oracle where it is known (kCases roots column);
        # otherwise PENDING -> the oracle phase (sturm) decides everything anyway.
        if source == "reuse" and not ora:
            ora = "PENDING"
        else:
            ora = ora if ora is not None else "PENDING"
        desc = f"t{table:02d} d{degree} b{bits}" + (f" tau={b}" if ctor == "nested_mignotte" else "")
        spec.append((name, family, table, degree, bits, ctor, a, b, c, seed,
                     source, suite_case or "", ora, achieved, desc))
        stats[source] += 1
        if source == "gen":
            glist.append(f"{name}\t{ctor}\t{a}\t{b}\t{c}\t{seed}")
        records.append({"id": len(records) + 1, "band": 1, "family": family,
                        "degree": degree, "desc": desc, "oracle": ora, "name": name})

    # ---- write outputs ----
    with open(os.path.join(OUT_DIR, "gen_spec.tsv"), "w") as fh:
        fh.write("# name\tfamily\ttable\tdegree\tbits_target\tctor\ta\tb\tc\tseed\t"
                 "source\tsuite_case\toracle\tachieved_bits\tdesc\n")
        for row in spec:
            fh.write("\t".join(str(x) for x in row) + "\n")
    with open(os.path.join(OUT_DIR, "gen_list.txt"), "w") as fh:
        for line in glist:
            fh.write(line + "\n")
    with open(os.path.join(OUT_DIR, "cases_record.json"), "w") as fh:
        json.dump(records, fh, indent=1)
    assert len(records) == 295 and len(set(r["name"] for r in records)) == 295

    # ---- report ----
    print(f"cases: {len(records)}  reuse={stats['reuse']}  generate={stats['gen']}")
    print("suite-reuse cases (suite case -> and name, achieved vs page column):")
    for row in spec:
        if row[10] == "reuse":
            fam, cls = row[1], BITS_CLASS[row[1]]
            tag = "" if cls == "EXACT" else f"  [{cls} recorded]"
            print(f"  case_{row[11]:<4} {row[0]:<42} suite_bits={row[13]:>6} "
                  f"page_b={row[4]:>6}{tag}")
    print(f"\ngenerate list: {len(glist)} rows -> and_gen_driver.cpp (deferred CPU phase):")
    print("  g++ -O2 -I Dsc/export/c_harness benchmark_results/and_bench/and_gen_driver.cpp "
          "-lgmp -o /tmp/and_gen_driver")
    print("  /tmp/and_gen_driver benchmark_results/and_bench/gen_list.txt "
          "benchmark_results/and_bench/coeffs")
    print("\noracle column: analytic-theorem where known; PENDING rows -> the oracle phase "
          "(sturm-count, deferred CPU). Gate G2 requires 295/295 determined.")
    return 0


if __name__ == "__main__":
    if "--materialize" in sys.argv:
        os.makedirs(COEFFS_DIR, exist_ok=True)
        n = 0
        for line in open(os.path.join(OUT_DIR, "gen_spec.tsv")):
            if line.startswith("#") or not line.strip():
                continue
            p = line.rstrip("\n").split("\t")
            if p[10] == "reuse":
                fam = suite_file_family(p[1], int(p[2]))
                src = os.path.join(SUITE_COEFFS, f"case_{p[11]}_{fam}.txt")
                dst = os.path.join(COEFFS_DIR, p[0] + ".txt")
                open(dst, "w").write(open(src).read())
                n += 1
        print(f"materialized {n} reuse files -> {COEFFS_DIR}")
        sys.exit(0)
    sys.exit(main())

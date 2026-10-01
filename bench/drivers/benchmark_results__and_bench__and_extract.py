#!/usr/bin/env python3
"""AND_BENCH manifest extractor: parse the 19 benchmark tables of the ANewDsc addendum page
(references/anewdsc_page_wayback-2016-12-04.html, Wayback capture 2016-12-04) into
benchmark_results/and_bench/manifest.tsv. Read-only; asserts the pre-registered counts.

Run from the repo root:  python3 benchmark_results/and_bench/and_extract.py

Output columns: name  table  family  degree  bitsize  anewdsc_s
  name      case id  and<tt>_<family>_d<deg>_b<bits>  (unique by construction)
  anewdsc_s the page's ANewDsc time in s (blank = no completion recorded, >600 s on 2016 HW)

Asserts (the track's contract, docs/AND_BENCH.md §2):
  - 19 tables parsed, 295 parameter points total
  - per-table counts: {1:22, 2:14, 3:9, 4:9, 5:20, 6:21, 7:9, 8:9, 9:9, 10:30, 11:17,
    12:26, 13:15, 14:16, 15:17, 16:17, 17:17, 18:9, 19:9}
  - per-family totals: nested_mignotte 36, mignotte_rat 47, mignotte_irr 41, gauss_sqrtn 20,
    gauss_logn 21, random_dense 17, random_monic 17, random_monic_lt1 17, resultant 16,
    chebyshev_T 9, chebyshev_U 9, hermite 9, laguerre 9, legendre 9, wilkinson 9,
    wilkinson_like 9
  - all case ids unique; all degrees/bitsizes positive ints
"""
import re
import sys
from collections import Counter

HTML = "references/anewdsc_page_wayback-2016-12-04.html"
OUT = "benchmark_results/and_bench/manifest.tsv"

# table id -> (family, kind) ; constructions live in the HTML captions (docs/AND_BENCH.md §1)
FAM = {
    1: "nested_mignotte", 2: "nested_mignotte",
    3: "chebyshev_T", 4: "chebyshev_U",
    5: "gauss_sqrtn", 6: "gauss_logn",
    7: "hermite", 8: "laguerre", 9: "legendre",
    10: "mignotte_rat", 11: "mignotte_rat", 12: "mignotte_irr", 13: "mignotte_irr",
    14: "resultant",
    15: "random_dense", 16: "random_monic", 17: "random_monic_lt1",
    18: "wilkinson_like", 19: "wilkinson",
}

EXPECT_TABLE_COUNTS = {1: 22, 2: 14, 3: 9, 4: 9, 5: 20, 6: 21, 7: 9, 8: 9, 9: 9,
                       10: 30, 11: 17, 12: 26, 13: 15, 14: 16, 15: 17, 16: 17,
                       17: 17, 18: 9, 19: 9}
EXPECT_FAMILY_TOTALS = Counter({
    "nested_mignotte": 36, "mignotte_rat": 47, "mignotte_irr": 41,
    "gauss_sqrtn": 20, "gauss_logn": 21, "random_dense": 17, "random_monic": 17,
    "random_monic_lt1": 17, "resultant": 16, "chebyshev_T": 9, "chebyshev_U": 9,
    "hermite": 9, "laguerre": 9, "legendre": 9, "wilkinson": 9, "wilkinson_like": 9,
})


def clean(s):
    return re.sub(r"\s+", " ", re.sub(r"<[^>]+>", "", s)).strip()


def main():
    html = open(HTML, errors="replace").read()
    tables = re.findall(r"<table.*?</table>", html, re.S)
    assert len(tables) == 19, f"expected 19 tables, got {len(tables)}"

    rows, per_table = [], {}
    for i, t in enumerate(tables, 1):
        trs = re.findall(r"<tr[^>]*>(.*?)</tr>", t, re.S)
        cells = []
        for r in trs:
            cs = [clean(c) for c in re.findall(r"<t[dh][^>]*>(.*?)</t[dh]>", r, re.S)]
            if cs:
                cells.append(cs)
        assert cells and cells[0][:2] == ["degree", "bitsize"], f"table {i}: header mismatch"
        n = 0
        for r in cells[1:]:
            if len(r) < 2 or not r[0].isdigit() or not r[1].isdigit():
                continue  # non-data rows (footers etc.)
            deg, bits = int(r[0]), int(r[1])
            anew = r[10] if len(r) > 10 and r[10] not in ("", "NaN") else ""
            rows.append((i, FAM[i], deg, bits, anew))
            n += 1
        per_table[i] = n

    assert per_table == EXPECT_TABLE_COUNTS, f"per-table mismatch: {per_table}"
    fam = Counter(r[1] for r in rows)
    assert fam == EXPECT_FAMILY_TOTALS, f"family mismatch: {fam}"
    assert len(rows) == 295, f"expected 295 rows, got {len(rows)}"

    names = [f"and{t:02d}_{f}_d{d}_b{b}" for t, f, d, b, _ in rows]
    assert len(set(names)) == len(names), "duplicate case ids"
    assert all(0 < d and 0 < b for *_, d, b, _ in [(t, f, d, b, a) for t, f, d, b, a in rows])

    with open(OUT, "w") as fh:
        fh.write("# AND_BENCH manifest: full ANewDsc benchmark axis, Wayback capture 2016-12-04\n")
        fh.write("# references/anewdsc_page_wayback-2016-12-04.html — 19 tables, 295 parameter points\n")
        fh.write("# columns: name  table  family  degree  bitsize  anewdsc_s(2016, blank=no completion)\n")
        for name, (t, fam_, d, b, a) in zip(names, rows):
            fh.write(f"{name}\t{t}\t{fam_}\t{d}\t{b}\t{a}\n")

    print(f"manifest: 295 rows, 19 tables -> {OUT}")
    print(f"families: {len(EXPECT_FAMILY_TOTALS)}, page-NaN rows: "
          f"{sum(1 for r in rows if not r[4])}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

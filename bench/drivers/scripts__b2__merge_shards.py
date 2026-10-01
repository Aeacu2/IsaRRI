#!/usr/bin/env python3
"""Merge the B2 window-check shards into one record per suite (2026-09-27).

  python3 scripts/b2/merge_shards.py

check_windows.py ran as parallel shards (--shard i/n), extra workers from the list's end (--reverse),
reruns (--dump-timeout) and the over-cap IsaRRI answer (--include-overcap). A case may therefore have
several rows. Per (case, poly) one row is kept, by precedence FAIL > OK > UNCHECKED > DUMP_TIMEOUT, so
a failure is never hidden by a later pass. The over-cap row gets credited=0, every other row
credited=1. An UNCHECKED row written before the alarm fix whose
timing line was printed is relabelled from "gp-died" to "over budget". Writes benchmark_results/b2_windows/{mpsolve,and}.tsv and prints the status counts.
"""
import collections, csv, glob, os

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
B2 = os.path.join(REPO, "benchmark_results/b2_windows")
RANK = {"FAIL": 0, "OK": 1, "UNCHECKED": 2, "DUMP_TIMEOUT": 3}


def merge(pattern, out, overcap=()):
    best, header = {}, None
    files = sorted(glob.glob(os.path.join(B2, pattern))) + [os.path.join(B2, f) for f in overcap]
    for path in files:
        with open(path) as f:
            r = csv.DictReader(f, delimiter="\t")
            header = header or r.fieldnames
            for row in r:
                row["credited"] = "0" if os.path.basename(path) in overcap else "1"
                # Rows written before the alarm fix (check_windows.py, 2026-09-27): gp printed its
                # timing line, so it did not die; the Sturm check ran out of its budget.
                if row["status"] == "UNCHECKED" and row["reasons"] == "gp-died" and row["check_s"] not in ("-", "-1", "-1.0"):
                    row["reasons"] = "over budget (e_ALARM)"
                k = (row["case"], row["poly"])
                if k not in best or RANK[row["status"]] < RANK[best[k]["status"]]:
                    best[k] = row
    # A DUMP_TIMEOUT row has poly "-"; once a later pass checked the case, that row is superseded.
    checked = {c for (c, q), r in best.items() if r["status"] != "DUMP_TIMEOUT"}
    best = {k: r for k, r in best.items() if not (r["status"] == "DUMP_TIMEOUT" and k[0] in checked)}
    cols = header + ["credited"]
    with open(os.path.join(B2, out), "w", newline="") as f:
        w = csv.DictWriter(f, cols, delimiter="\t", lineterminator="\n")
        w.writeheader()
        for k in sorted(best):
            w.writerow(best[k])
    c = collections.Counter((r["credited"], r["status"]) for r in best.values())
    print(out, "from", [os.path.basename(p) for p in files], dict(c))


merge("mpsolve_s*.tsv", "mpsolve.tsv")
merge("and_s*.tsv", "and.tsv", overcap=("and_overcap.tsv",))

#!/usr/bin/env python3
"""SMT-BENCH Phase 2 extraction: distinct A-polynomial workload per fired instance.

Input : results/probe_run1.tsv + dumps/phase1/<logic>/<family>/<inst>.tsv (dump-format
        lines "A\\t<deg>\\t<c0>,<c1>,..."; B lines ignored).
Output: extracted/<logic>__<family>__<inst>.apolys  (one distinct A poly per line,
        dump format, first-encounter order)  and
        extracted/manifest.tsv  (instance, ndistinct, nA_calls, total_deg, max_deg,
        max_digits, roots_oracle if computed).
Counts are load-insensitive; the squarefree spot-check on a sample is also fine here.
"""
import csv
import glob
import os
import sys
import math
from collections import defaultdict

sys.set_int_max_str_digits(0)

DUMPS = "benchmark_results/smt_bench/dumps/phase1"
OUT = "benchmark_results/smt_bench/extracted"


def expected_stem(corpus, instance, root):
    inst_dir = os.path.join(root, corpus)
    hits = sorted(glob.glob(os.path.join(inst_dir, "**", instance), recursive=True))
    if not hits:
        return None
    rel = os.path.relpath(hits[0], inst_dir)
    return os.path.splitext(rel)[0].replace("/", "__")


def main():
    os.makedirs(OUT, exist_ok=True)
    rows = list(csv.DictReader(open("benchmark_results/smt_bench/results/probe_run1.tsv"),
                               delimiter="\t"))
    fired = [r for r in rows if int(r["nA"]) + int(r["nB"]) > 0]
    root = "benchmark_results/smt_bench/corpus_phase1"
    stem_cache = {}
    manifest = []
    n_skip_missing = 0
    sqf_check = []  # (instance, ndistinct, n_squarefree) for the spot-check sample

    for r in fired:
        inst_key = f"{r['corpus']}__{r['instance']}".replace("/", "_")
        if r["corpus"] not in stem_cache:
            stem_cache[r["corpus"]] = {}
        stem = stem_cache[r["corpus"]].get(r["instance"])
        if stem is None:
            stem = expected_stem(r["corpus"], r["instance"], root)
            stem_cache[r["corpus"]][r["instance"]] = stem
        if stem is None:
            n_skip_missing += 1
            continue
        dump_path = os.path.join(DUMPS, r["corpus"], stem + ".tsv")
        if not os.path.exists(dump_path):
            n_skip_missing += 1
            continue
        distinct = []        # list of (deg, coeffs)
        seen = set()
        mult = defaultdict(int)
        nA = 0
        for line in open(dump_path, errors="replace"):
                parts = line.rstrip("\n").split("\t")
                if len(parts) < 3 or parts[0] != "A":
                    continue
                deg = int(parts[1])
                coeffs = parts[2]
                nA += 1
                key = (deg, coeffs)
                mult[key] += 1
                if key not in seen:
                    seen.add(key)
                    distinct.append(key)
        if not distinct:
            continue  # nA>0 per TSV but no A lines in dump (should not happen)
        with open(os.path.join(OUT, inst_key + ".apolys"), "w") as fh:
            for deg, coeffs in distinct:
                fh.write(f"A\t{deg}\t{coeffs}\n")
        max_deg = max(d for d, _ in distinct)
        tot_deg = sum(d for d, _ in distinct)
        max_digits = max(len(c) for _, c in distinct) if distinct else 0
        manifest.append({
            "instance": inst_key, "corpus": r["corpus"], "nA": nA,
            "ndistinct": len(distinct), "max_deg": max_deg, "tot_deg": tot_deg,
            "max_digits": max_digits,
            "top_multiplicity": max(mult.values()),
        })
        # squarefree spot-check: sample a few polys from a few instances
        if len(sqf_check) < 25 and len(distinct) <= 200:
            sqf_check.append((inst_key, distinct[:20]))

    with open(os.path.join(OUT, "manifest.tsv"), "w", newline="") as fh:
        w = csv.DictWriter(fh, delimiter="\t",
                           fieldnames=["instance", "corpus", "nA", "ndistinct",
                                       "max_deg", "tot_deg", "max_digits",
                                       "top_multiplicity"])
        w.writeheader()
        for m in manifest:
            w.writerow(m)

    nd = len(manifest)
    total_distinct = sum(m["ndistinct"] for m in manifest)
    total_calls = sum(m["nA"] for m in manifest)
    print(f"instances: {nd} (skipped missing dump: {n_skip_missing})")
    print(f"total distinct A polys: {total_distinct:,}  total A calls: {total_calls:,}")
    print(f"distinct-per-instance: max {max(m['ndistinct'] for m in manifest):,} "
          f"median {sorted(m['ndistinct'] for m in manifest)[nd // 2]:,}")
    big = sorted(manifest, key=lambda m: -m["ndistinct"])[:10]
    for m in big:
        print(f"  {m['corpus']}/{m['instance'][:60]} distinct={m['ndistinct']:,} "
              f"calls={m['nA']:,} maxdeg={m['max_deg']} digits={m['max_digits']}")

    print(f"\nsquarefree spot-check instances: {len(sqf_check)}")
    nsqf = 0
    for inst, polys in sqf_check:
        from sympy import Poly, symbols
        x = symbols("x")
        bad = 0
        for deg, cs in polys:
            p = Poly([int(v) for v in cs.split(",")], x)
            g = Poly(p).gcd(Poly(p.diff()))
            if g.degree() > 0:
                bad += 1
        if bad:
            print(f"  {inst}: {bad}/{len(polys)} NOT squarefree")
        else:
            nsqf += 1
    print(f"fully squarefree instances: {nsqf}/{len(sqf_check)}")


if __name__ == "__main__":
    main()

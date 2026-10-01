#!/usr/bin/env python3
"""Astra 4.1 (2026-09-27): how much does moving IsaRRI's output allocation and initialisation inside
the timer change SMT-Bench? ONE binary, two arms selected by DSC_ALLOC_IN_TIMER (no cross-binary
layout floor): A = campaign timed region (call only), B = allocation + initialisation + call, C = minimal per-call allocation + initialisation + call,
M = msolve (same session, campaign harness).
Same instances (the 326 of campaign 2), 5 reps, arms alternating per instance with rotating order;
per-instance minimum over reps, as the campaign scores. Freeing stays outside both, as for every
competitor. Writes one row per (instance, rep, arm) and prints the summary.

  alloc_ab.py <binary> <out.tsv>
"""
import csv, os, statistics, subprocess, sys

REPO = os.path.expanduser("~/Desktop/Dsc_LLVM")
SMT = os.path.join(REPO, "benchmark_results/smt_bench")
BIN, OUT = sys.argv[1], sys.argv[2]
REC = os.path.join(SMT, "results/campaign2_run1.tsv")

rec = {}
for line in open(REC):
    if line.startswith("#"):
        continue
    f = line.rstrip("\n").split("\t")
    if f[1] in ("powsub_l4", "msolve") and f[3] in ("OK", "SLOW"):
        k = (f[0], f[1])
        rec[k] = min(rec.get(k, 1e18), float(f[5]))
insts = sorted({i for (i, a) in rec if a == "powsub_l4"})
assert len(insts) == 326, len(insts)


MSOLVE = os.path.join(REPO, "Dsc/export/c_harness/build/all_roots_vs_competitors_bench")


def run(inst, arm):
    if arm == "M":
        with open(os.path.join(SMT, "extracted", inst + ".apolys")) as fi:
            out = subprocess.run([MSOLVE, "--solve-stdin-multi", inst, "msolve"], stdin=fi,
                                 capture_output=True, text=True, timeout=60).stdout
        kv = dict(x.split("=", 1) for x in out.strip().splitlines()[-1].split(",")[1:])
        return float(kv["msolve_ms"]), int(kv["msolve_roots"])
    env = dict(os.environ)
    env.pop("DSC_ALLOC_IN_TIMER", None); env.pop("DSC_ALLOC_MIN", None)
    if arm == "B":
        env["DSC_ALLOC_IN_TIMER"] = "1"
    if arm == "C":
        env["DSC_ALLOC_MIN"] = "1"
    with open(os.path.join(SMT, "extracted", inst + ".apolys")) as fi:
        out = subprocess.run([BIN, "--solve-stdin-multi", inst, "powsub", "16"], stdin=fi, env=env,
                             capture_output=True, text=True, timeout=60).stdout
    last = out.strip().splitlines()[-1]
    kv = dict(x.split("=", 1) for x in last.split(",")[1:])
    return float(kv["powsub_ms"]), int(kv["powsub_roots"])


rows = []
with open(OUT, "w") as fo:
    fo.write("instance\trep\tarm\tms\troots\n")
    for rep in range(5):
        for n, inst in enumerate(insts):
            arms = ("A", "B", "C", "M")
            k = (n + rep) % 4
            order = arms[k:] + arms[:k]
            for arm in order:
                ms, roots = run(inst, arm)
                fo.write(f"{inst}\t{rep}\t{arm}\t{ms}\t{roots}\n")
                rows.append((inst, arm, ms))
        fo.flush()
        print("rep", rep, "done", flush=True)

best = {}
for inst, arm, ms in rows:
    best[(inst, arm)] = min(best.get((inst, arm), 1e18), ms)
par2 = lambda arm: statistics.fmean(best[(i, arm)] if best[(i, arm)] <= 1000 else 2000 for i in insts)
a, b, c = par2("A"), par2("B"), par2("C")
print(f"C (minimal alloc+init+call) {c:.3f}; C-A {c-a:.3f} ({100*(c-a)/a:.1f}%)")
m = statistics.fmean(rec[(i, "msolve")] if rec[(i, "msolve")] <= 1000 else 2000 for i in insts)
ms_now = par2("M")
print(f"same-session msolve PAR2 {ms_now:.3f}")
r = statistics.fmean(rec[(i, "powsub_l4")] if rec[(i, "powsub_l4")] <= 1000 else 2000 for i in insts)
print(f"PAR2 ms per instance: A (call only) {a:.3f}; B (alloc+init+call) {b:.3f}; B-A {b-a:.3f} ({100*(b-a)/a:.1f}%)")
print(f"recorded campaign: IsaRRI {r:.3f}, msolve {m:.3f}")
import math
for arm in ("A", "B", "C"):
    fa = sum(best[(i, arm)] < best[(i, "M")] for i in insts)
    g = math.exp(statistics.fmean(math.log(best[(i, arm)] / best[(i, "M")]) for i in insts))
    print(f"arm {arm} vs same-session msolve: faster on {fa}/326, paired geomean {g:.3f}")

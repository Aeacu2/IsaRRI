#!/usr/bin/env python3
"""isarri-hash-compare.py -- supplement plan phase 4: the renamed artifact emits the same windows.

Runs `powsub_hash_isarri` (powsub_hash.cpp linked against IsaRRI's export/isarri.ll, with
`-Dall_dsc_powsub_main=isarri`) over every case on which the T-e pass recorded an L4 hash, and
compares root count and window hash with that recorded value
(benchmark_results/data/thesis_campaign_2026-09-12/hash_compare.tsv, `powsub_hash_l4` = 0561bdc3).

Cases T-e recorded as BOTH_CAPPED or ERROR carry no L4 hash and are not run. The L4 driver is not
re-run: its hashes are the recorded ones.

This is a COUNT, not a timing: no clock is read. The cap only bounds a hang; it is set well above
the campaign's 150 s so that a slow case on a loaded machine is not mistaken for a difference, and a
case that still caps is reported TIMEOUT (uncompared), never MISMATCH.

Usage:
  python3 scripts/gates/isarri-hash-compare.py --out <out.tsv> [--and-one-per-family]   (resume-safe)

--and-one-per-family keeps every SMT and MPSolve case but only one AND case per family: an
already-compared one if the output has it, else the lowest-degree case with a recorded hash. The
body-level diff (scripts/isarri-ll-equiv.py) is the equivalence evidence; this is a spot check.
Exit status: 0 = every compared case matches and none failed to run; 1 otherwise.
Output TSV: suite, case, status, roots_l4, roots_isarri, hash_l4, hash_isarri,
where status in {MATCH, MISMATCH, TIMEOUT, ERROR}.
"""
import argparse
import csv
import importlib.util
import os
import signal
import sys

REPO = "/Users/aeacu2/Desktop/Dsc_LLVM"
BINARY = f"{REPO}/Dsc/export/c_harness/build/powsub_hash_isarri"
RECORDED = f"{REPO}/benchmark_results/data/thesis_campaign_2026-09-12/hash_compare.tsv"
CAP = 600

_spec = importlib.util.spec_from_file_location("te", f"{REPO}/scripts/gates/powsub-hash-compare.py")
te = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(te)
te.CAP = CAP  # run_one waits CAP + 15 s


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--and-one-per-family", action="store_true")
    args = ap.parse_args()
    signal.signal(signal.SIGTERM, te._on_signal)
    signal.signal(signal.SIGINT, te._on_signal)

    recorded = {}
    with open(RECORDED, newline="") as fh:
        for row in csv.DictReader(fh, delimiter="\t"):
            if row["hash_l4"] and not row["hash_l4"].startswith(("TIMEOUT", "ERROR")) and row["roots_l4"]:
                recorded[(row["suite"], row["case"])] = (int(row["roots_l4"]), row["hash_l4"])

    done = set()
    if os.path.exists(args.out):
        with open(args.out, newline="") as fh:
            for row in csv.DictReader(fh, delimiter="\t"):
                done.add((row["suite"], row["case"]))
    new = not os.path.exists(args.out)
    cases = [c for c in te.load_cases() if (c[0], c[1]) in recorded]
    if args.and_one_per_family:
        import json
        meta = {r["name"]: r for r in json.load(open(f"{REPO}/benchmark_results/and_bench/cases_record.json"))}
        pick = {}
        for c in cases:
            if c[0] != "and":
                continue
            m = meta[c[1]]
            key = (0 if ("and", c[1]) in done else 1, int(m.get("degree") or 0), c[1])
            if m["family"] not in pick or key < pick[m["family"]][0]:
                pick[m["family"]] = (key, c)
        chosen = {v[1][1] for v in pick.values()}
        cases = [c for c in cases if c[0] != "and" or c[1] in chosen]
        print(f"AND families: {len(pick)}", flush=True)
    print(f"cases with a recorded L4 hash: {len(recorded)}; loaded: {len(cases)}; already done: {len(done)}",
          flush=True)
    with open(args.out, "a", newline="") as fh:
        w = csv.writer(fh, delimiter="\t", lineterminator="\n")
        if new:
            w.writerow(["suite", "case", "status", "roots_l4", "roots_isarri", "hash_l4", "hash_isarri"])
        for suite, case, path in cases:
            if (suite, case) in done:
                continue
            r4, h4 = recorded[(suite, case)]
            r, h = te.run_one(BINARY, case, path)
            if r is None:
                status = "TIMEOUT" if h == "TIMEOUT" else "ERROR"
            else:
                status = "MATCH" if (r, h) == (r4, h4) else "MISMATCH"
            w.writerow([suite, case, status, r4, "" if r is None else r, h4, h])
            fh.flush()
            print(f"{suite}\t{case}\t{status}", flush=True)

    counts = {}
    with open(args.out, newline="") as fh:
        for row in csv.DictReader(fh, delimiter="\t"):
            counts[row["status"]] = counts.get(row["status"], 0) + 1
    print("summary:", counts, flush=True)
    sys.exit(0 if set(counts) <= {"MATCH"} and counts.get("MATCH", 0) >= len(cases) else 1)


if __name__ == "__main__":
    main()

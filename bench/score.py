#!/usr/bin/env python3
"""score.py -- the thesis's per-suite result tables (Chapter 7), computed from bench/results/.

  python3 bench/score.py                 all three suites
  python3 bench/score.py smt             one suite (smt | mpsolve | and)
  python3 bench/score.py and --cap 90    AND-Bench scored at a lower cap (at most 180 s)
  python3 bench/score.py spread          run-to-run spread on MPSolve-Bench and AND-Bench

The rows are those of the thesis's campaign (18-19 September 2026, UTC): nine arms, each timed on
the same task (isolate the real roots of a squarefree integer polynomial, with no squarefree
preprocessing and no refinement): IsaRRI, msolve, anewdsc (ANewDsc, default configuration),
sage, pari, z3, cgal, libpoly, which are ranked, and anewdsc_i0 (ANewDsc with -i 0), a reference
configuration of the same tool, printed below the ranked arms. A run is a timeout when its
reported solve time exceeds the cap; a process is killed only at the cap plus 15 s of wall time.
bench/README.md describes the protocol and the file formats.

Scoring: one cell per (case, arm); PAR2 is the mean over all cases, charging each cell its
recorded time if it is done and twice the cap C otherwise.

SMT-Bench      results/smt.tsv, 326 instances x 5 runs, C = 1 s. One row per run.
  cell = minimum over the arm's OK runs; the reference count is Z3's for the instance.
  wrong:   some OK run's count differs from the reference     -> 2C
  timeout: no OK run                                          -> 2C
  slow:    done, but the cell exceeds C (not stopped at C)    -> 2C
  PAR2 and geometric mean in ms.

MPSolve-Bench  results/mpsolve.csv, 131 cases x 3 runs, C = 60 s.
AND-Bench      results/and.csv, 295 cases, run at 180 s (at most 2 runs; a case ends at its
               first timed-out run) and scored at C = 150 s: a run over C is a timeout, and the
               ladder rule is applied again (once an arm times out or errs on a rung of a table,
               the larger rungs of that table are skipped).
  One row per (case, arm), already the minimum over the arm's completed runs. The reference is a
  Sturm or analytic count; -1 marks a case without one, where any completion counts as done.
  wrong:   OK with a count other than a determined reference  -> 2C
  timeout / skipped / error: TIMEOUT / SKIPPED / ERROR        -> 2C
  PAR2 in s; geometric mean in ms.

The geometric mean is over the arm's completed cells with positive time. Column headings:
done, wrong (wrg), error (err), timeout (tmo), skipped (skp), slow.

spread: for every (case, arm) with at least two completed runs of at least 1 s in
results/campaign.log, the relative difference between its slowest and fastest run; prints the
number of such pairs, the median, the 95th percentile (nearest rank) and the maximum.
"""
import collections
import csv
import math
import os
import re
import statistics
import sys

HERE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
ARMS = ["IsaRRI", "msolve", "anewdsc", "anewdsc_i0", "sage", "pari", "z3", "cgal", "libpoly"]


def ranked(arms, key):
    """The eight ranked arms by PAR2, then the reference configuration anewdsc_i0 (not ranked)."""
    return sorted((a for a in arms if a != "anewdsc_i0"), key=key) + \
        [a for a in arms if a == "anewdsc_i0"]


def smt():
    C = 1000.0
    rows = []
    with open(os.path.join(HERE, "smt.tsv")) as fh:
        hdr = None
        for line in fh:
            if line.startswith("#") or not line.strip():
                continue
            f = line.rstrip("\n").split("\t")
            if hdr is None:
                hdr = f
                continue
            rows.append(dict(zip(hdr, f)))
    oracle = {}
    for x in rows:
        if x["arm"] == "z3" and x["status"] == "OK":
            oracle.setdefault(x["instance"], set()).add(int(x["roots"]))
    bad = [i for i, v in oracle.items() if len(v) != 1]
    if bad:
        sys.exit(f"Z3 reference count not unique on {len(bad)} instances")
    n = len({x["instance"] for x in rows})
    cells = collections.defaultdict(list)
    for x in rows:
        cells[(x["instance"], x["arm"])].append(x)
    res = collections.defaultdict(lambda: dict(done=0, mis=0, tou=0, slow=0, par=0.0, vals=[]))
    for (inst, arm), xs in cells.items():
        o = next(iter(oracle[inst]))
        ok = [x for x in xs if x["status"] == "OK"]
        r = res[arm]
        if any(int(x["roots"]) != o for x in ok):
            r["mis"] += 1
            r["par"] += 2 * C
            continue
        if not ok:
            r["tou"] += 1
            r["par"] += 2 * C
            continue
        v = min(float(x["ms"]) for x in ok)
        r["done"] += 1
        if v > C:
            r["slow"] += 1
            r["par"] += 2 * C
        else:
            r["par"] += v
        if v > 0:
            r["vals"].append(v)
    print(f"SMT-Bench: {n} instances, cap 1 s, PAR2 and geometric mean in ms")
    print(f"{'arm':12s} {'done':>5s} {'wrg':>4s} {'tmo':>4s} {'slow':>5s} {'PAR2':>9s} {'geo.mean':>8s}")
    for arm in ranked(res, lambda a: res[a]["par"]):
        r = res[arm]
        g = math.exp(statistics.fmean(map(math.log, r["vals"])))
        print(f"{arm:12s} {r['done']:5d} {r['mis']:4d} {r['tou']:4d} {r['slow']:5d} "
              f"{r['par'] / n:9.3f} {g:8.3f}")


def rescore(rows, cap_ms):
    """Rows as a run at cap_ms would have recorded them: a completed run over cap_ms becomes a
    TIMEOUT, and the ladder skip is replayed per (arm, family, ladder)."""
    out, failed = [], {}
    for x in sorted(rows, key=lambda x: (x["solver"], int(x["band"]), x["case"])):
        y = dict(x)
        key = (y["solver"], y["family"], y["params"].split()[0])
        b = int(y["band"])
        if not y["status"].startswith("SKIPPED") and key in failed and b > failed[key]:
            y["status"], y["roots"], y["ms"] = f"SKIPPED(rescore>=B{failed[key]})", "-1", "-1"
        elif y["status"] == "OK" and float(y["ms"]) > cap_ms:
            y["status"], y["roots"], y["ms"] = "TIMEOUT", "-1", str(cap_ms)
        if y["status"] != "OK" and not y["status"].startswith("SKIPPED"):
            failed.setdefault(key, b)
        out.append(y)
    return out


def capped(name, title, cap_s, run_cap_s):
    C = cap_s * 1000.0
    with open(os.path.join(HERE, name), newline="") as fh:
        rows = list(csv.DictReader(fh))
    if cap_s > run_cap_s:
        sys.exit(f"{title} cannot be scored above the cap it was run at ({run_cap_s:g} s)")
    if run_cap_s > cap_s:
        rows = rescore(rows, C)
    n = len({x["case"] for x in rows})
    cnt = collections.defaultdict(collections.Counter)
    par = collections.defaultdict(float)
    ms = collections.defaultdict(list)
    for x in rows:
        a, s, o = x["solver"], x["status"], int(x["oracle"])
        if s == "OK" and (o < 0 or int(x["roots"]) == o):
            cnt[a]["done"] += 1
            par[a] += float(x["ms"])
            if float(x["ms"]) > 0:
                ms[a].append(float(x["ms"]))
        else:
            par[a] += 2 * C
            k = "mis" if s == "OK" else "tou" if s == "TIMEOUT" else "skip" if s.startswith("SKIPPED") else "err"
            cnt[a][k] += 1
    run = f", run at {run_cap_s:g} s" if run_cap_s > cap_s else ""
    print(f"{title}: {n} cases, cap {cap_s:g} s{run}, PAR2 in s, geometric mean in ms")
    print(f"{'arm':12s} {'done':>5s} {'wrg':>4s} {'err':>4s} {'tmo':>4s} {'skp':>5s} {'PAR2':>8s} {'geo.mean':>9s}")
    for a in ranked(cnt, lambda a: par[a]):
        g = math.exp(statistics.fmean(map(math.log, ms[a]))) if ms[a] else float("nan")
        c = cnt[a]
        print(f"{a:12s} {c['done']:5d} {c['mis']:4d} {c['err']:4d} {c['tou']:4d} {c['skip']:5d} "
              f"{par[a] / n / 1000:8.3f} {g:9.1f}")


def spread():
    reps = collections.defaultdict(list)
    with open(os.path.join(HERE, "campaign.log"), errors="replace") as fh:
        for line in fh:
            m = re.match(r"\s+(\S+)/(\S+) rep\d+ OK roots=-?\d+ ([\d.]+)ms", line)
            if m:
                reps[(m.group(1), m.group(2))].append(float(m.group(3)))
    sp = sorted(max(v) / min(v) - 1 for v in reps.values() if len(v) >= 2 and min(v) >= 1000)
    p95 = sp[max(0, -(-95 * len(sp) // 100) - 1)]
    print(f"Run-to-run spread (MPSolve-Bench and AND-Bench, runs of at least 1 s): {len(sp)} "
          f"case-arm pairs; median {100 * sp[len(sp) // 2]:.2f}%, 95th percentile "
          f"{100 * p95:.2f}%, maximum {100 * sp[-1]:.2f}%")


if __name__ == "__main__":
    args = sys.argv[1:]
    and_cap = 150.0
    if "--cap" in args:
        i = args.index("--cap")
        and_cap = float(args[i + 1])
        del args[i:i + 2]
    SUITES = {"smt": smt,
              "mpsolve": lambda: capped("mpsolve.csv", "MPSolve-Bench", 60.0, 60.0),
              "and": lambda: capped("and.csv", "AND-Bench", and_cap, 180.0),
              "spread": spread}
    for i, s in enumerate(args or ["smt", "mpsolve", "and"]):
        if s not in SUITES:
            sys.exit(__doc__)
        if i:
            print()
        SUITES[s]()

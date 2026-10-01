#!/usr/bin/env python3
"""final-suite-run.py -- the FINAL_BENCHMARK_SUITE driver (calibration + record run).

Runbook: docs/FINAL_BENCHMARK_PLAN.md   Design: docs/FINAL_BENCHMARK_SUITE.md

Adapted from benchmark_results/summaries/competitors_suite_v2_2026-07-21/run_all.py -- the
per-solver invocation contracts there are proven working and are reproduced verbatim. What is
new here is the case source (the 125-row cached suite), the solver subsetting, and the D4
timeout policy.

D4 timeout policy (PLAN §1, SUITE §8.3):
  a. no repeat on timeout            -- a capped row is recorded once, never re-run
  b. skip harder rows in the family  -- after a TIMEOUT, that solver skips higher bands
  c. SKIPPED != TIMEOUT              -- reported as its own status; never folded into either
  d. TIMEOUT triggers the skip; ERROR/PARSE_ERROR NEVER does (crashes are non-monotone)
  e. "harder" = calibrated band order, never parameter size

Cases are visited family-major, band ascending, with the solver loop innermost -- this
satisfies both the per-case interleaving law and (b).

  calibration:  ./final-suite-run.py --mode calibrate --cap 150 --reps 1
  record run:   ./final-suite-run.py --mode record    --cap 150 --reps 3

CAP = 150 s (user decision 2026-08-01), down from 300. Every completion count in this
campaign is defined by it, so it is stated wherever a rate is reported. B5 is
correspondingly 60-150 s, not 60-300 s.
"""
import argparse
import atexit
import collections
import csv
import json
import os
import re
import signal
import subprocess
import sys
import time

# 🔴 2026-08-04: the universal 8 GB memory rule (CALIBRATION_RUNBOOK §5.4, user decision) is
# implemented where the platform allows and documented where it cannot:
#   - pari: parisizemax = 8 GB (PARI_SIZEMAX below) -- gp's OWN allocator ceiling, enforced by
#     gp itself. This is the rule's real work: every >6 GB row in the record run was a pari row.
#   - everything else: NOT OS-enforceable on macOS. Verified 2026-08-04 (macOS 26.5.2): the
#     kernel rejects ANY finite RLIMIT_AS with EINVAL (errno 22, via both Python resource and
#     raw ctypes setrlimit; only RLIM_INFINITY is accepted) and `ulimit -v` likewise fails.
#     There is no OS memory cap for arbitrary children here. The de-facto bound is the
#     machine: 16 GB RAM, one job at a time, 150 s cap. No solver but pari has ever needed
#     more in this campaign.

# 🔴 Killing this driver with `pkill -f final-suite-run.py` kills the PARENT ONLY -- its
# in-flight solver child (gp / sage / anewdsc / all_roots_vs_competitors_bench) is reparented to
# init and keeps burning a core. On 2026-08-01 three such orphans (77% + 61% + 100% CPU)
# survived two kills and inflated every subsequent measurement ~1.9x, which was very nearly
# mis-attributed to a code change. Guard both ends:
#   - this driver kills its own process group on the way out, and
#   - LAUNCH IT WITH `setsid` and STOP IT WITH `kill -- -<pgid>` (see FINAL_BENCHMARK_PLAN.md).
# Always confirm a clean machine before trusting a timing:
#   ps ax -o pid,ppid,%cpu,comm | grep -Ei 'all_roots|gp$|sage|descartes|suite_v2_bench'
def _kill_own_group():
    try:
        os.killpg(os.getpgid(0), signal.SIGKILL)
    except Exception:
        pass


def _on_signal(signum, _frame):
    _reap_children()
    _kill_own_group()
    os._exit(128 + signum)


# 🔴 subprocess.run(timeout=...) kills only the DIRECT child. Two solvers here launch a
# grandchild: `sage` is a wrapper that execs sage_solve_one.sage.py, and anewdsc_bench.py
# spawns test_descartes_osx. On timeout the wrapper dies and the WORKER SURVIVES at ~100% CPU,
# silently inflating every later timing. Measured 2026-08-01: one leaked sage worker ran 6:43
# at 99.3% CPU and its family of timeouts would have leaked one per B4/B5 row, compounding.
# Fix: every child gets its OWN process group (start_new_session) and on timeout we kill the
# whole GROUP, not the process. _LIVE_GROUPS + atexit covers the case where the driver dies.
_LIVE_GROUPS = set()


def _killpg(pid):
    try:
        os.killpg(os.getpgid(pid), signal.SIGKILL)
    except Exception:
        try:
            os.kill(pid, signal.SIGKILL)
        except Exception:
            pass


def _reap_children():
    for pid in list(_LIVE_GROUPS):
        _killpg(pid)
    _LIVE_GROUPS.clear()


atexit.register(_reap_children)


def _preflight(where):
    """Strict bench-guard check before a measurement (startup, each row, after each rep
    timeout). BLOCKS until the gate is clean, re-checking every 10 s — a busy window or
    a leaked worker PAUSES the run instead of failing it, so the run proceeds whenever
    the machine is free (the user wants it to eventually run, not to abort). The full
    offender list is printed on the first failure, then a short line every ~30 s so a
    long wait stays visible in the log. bench-guard excludes a driver in ITS ancestry;
    a LEAKED worker from an earlier timeout is reparented (PPID 1), is not in that
    chain, and so blocks here until reaped (`bench-guard.sh --reap`) — the record's
    lsr1/msolve cell fell to exactly that leak running on into the next measurement.
    """
    quiet = 0
    while True:
        g = subprocess.run([GUARD, "--check", "--strict"], capture_output=True, text=True)
        if g.returncode == 0:
            return
        quiet += 1
        if quiet == 1 or quiet % 3 == 0:
            sys.stderr.write(g.stdout)
            sys.stderr.write(f"=== blocked before {where} (re-checking every 10s; "
                             f"a leak needs: {GUARD} --reap)\n")
        time.sleep(10)


# ---- campaign-2 guard policy (2026-09-19, user) ------------------------------------------------
# Campaign 1 lost hours to _preflight BLOCKING on transient macOS daemon spikes: it ran before every
# case AND after every timed-out rep (30 of its 34 logged blocks were post-timeout). Campaign 2:
#   * the BLOCKING strict check runs once per family (its first case) and at launch;
#   * every other case runs the same check NON-blocking and appends any foreign CPU to
#     <out>.guard.tsv, so the affected cases can be re-measured (plan §5.3) instead of waited on;
#   * after a timed-out rep only true ORPHANS are reaped (`bench-guard.sh --reap`, non-strict,
#     never waits) -- orphan leaks, not daemon spikes, are what the post-timeout check was for.
GUARD_SEEN_FAMILIES = set()
GUARD_LOG = None


def _note_foreign(where):
    g = subprocess.run([GUARD, "--check", "--strict"], capture_output=True, text=True)
    if g.returncode != 0 and GUARD_LOG:
        offenders = " | ".join(l.strip() for l in g.stdout.splitlines() if l.strip().startswith("pid="))
        with open(GUARD_LOG, "a") as fh:
            fh.write(f"{time.strftime('%Y-%m-%dT%H:%M:%S')}\t{where}\t{offenders}\n")
        print(f"    guard: foreign CPU before {where} (logged, not waited on): {offenders[:150]}",
              file=sys.stderr)


def _after_timeout(where):
    if not CAMPAIGN2:
        _preflight(where)
        return
    g = subprocess.run([GUARD, "--reap"], capture_output=True, text=True)
    if "killed" in g.stdout:
        print(f"    guard: reaped orphans after {where}: {g.stdout.strip()[:200]}", file=sys.stderr)
        if GUARD_LOG:
            with open(GUARD_LOG, "a") as fh:
                fh.write(f"{time.strftime('%Y-%m-%dT%H:%M:%S')}\treaped after {where}\t"
                         f"{' '.join(g.stdout.split())[:300]}\n")


def _run(cmd, timeout, stdin=None, text_input=None, cwd=None):
    """Run cmd in its own process group. Returns (rc, stdout, stderr, timed_out)."""
    p = subprocess.Popen(cmd, stdin=(stdin if stdin is not None else
                                     (subprocess.PIPE if text_input is not None else None)),
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         cwd=cwd, start_new_session=True)
    _LIVE_GROUPS.add(p.pid)
    try:
        out, err = p.communicate(input=text_input, timeout=timeout)
        return p.returncode, out, err, False
    except subprocess.TimeoutExpired:
        _killpg(p.pid)
        try:
            p.communicate(timeout=10)
        except Exception:
            pass
        return -1, "", "", True
    finally:
        _LIVE_GROUPS.discard(p.pid)

REPO = "/Users/aeacu2/Desktop/Dsc_LLVM"
GUARD = f"{REPO}/scripts/bench-guard.sh"
HARNESS = f"{REPO}/Dsc/export/c_harness"
COEFFS = f"{REPO}/benchmark_results/final_suite/coeffs"
CASES_HPP = f"{HARNESS}/final_suite_cases.hpp"

ALL_ROOTS_BIN = f"{HARNESS}/build/all_roots_vs_competitors_bench"
CGAL_BIN = f"{HARNESS}/build/cgal_descartes_bench"
ANEWDSC_BIN = os.path.expanduser("~/Downloads/test_descartes_osx")
PARI_SCRIPT = f"{HARNESS}/pari_solve_one.gp"
SAGE_SCRIPT = f"{HARNESS}/sage_solve_one.sage"
# sagesqf (2026-09-18): real_roots(f, skip_squarefree=True) -- see the header of that script.
SAGE_SQF_SCRIPT = f"{HARNESS}/sage_solve_one_sqf.sage"
ANEWDSC_PY = f"{HARNESS}/anewdsc_bench.py"

ONLY_SOLVERS = []
CAMPAIGN2 = False
INPROCESS = ("ours", "z3", "msolve", "libpoly", "arb", "z3sqf", "parisqf", "libpolysqf")
# z3sqf (2026-09-18): z3's sqf_isolate_roots -- the call the SMT-BENCH leg times -- via the standalone
# z3_allroots_timer (same Z3UPoly construction and timed region as all_roots_vs_competitors_bench's z3
# arm, minus the square_free gcd). Every MPSolve/AND input is certified squarefree
# (benchmark_results/{mpsolve_suite,and_bench}/sqfree_gate_2026-09-18.csv).
Z3T_BIN = f"{HARNESS}/build/z3_allroots_timer"
# Thesis campaign 2 (2026-09-18): every competitor timed on the same task as IsaRRI -- isolation of a
# squarefree input, no squarefree preprocessing, isolation only (docs/THESIS_CAMPAIGN2_PLAN.md).
#   parisqf    pari_timer: PARI's realroots minus ZX_squff, isolating intervals, in-process timer
#   libpolysqf libpoly_nosqf_timer: patched libpoly (no squarefree factorisation), isolation call only
INPROC_BIN = {"z3sqf": Z3T_BIN,
              "parisqf": f"{HARNESS}/build/pari_timer",
              "libpolysqf": f"{HARNESS}/build/libpoly_nosqf_timer"}
CAMPAIGN2_SOLVERS = ["powsub_l4", "msolve", "anewdsc", "anewdsc_i0", "sagesqf", "parisqf", "z3sqf",
                     "cgal", "libpolysqf"]
# anewdsc_i0 (2026-09-19): anewdsc -S 1 -i 0, a sensitivity arm beside the default config. The
# default -i 1 is labelled [EXPERIMENTAL] in the tool's -h and causes 12/16 of its MPSolve/AND
# miscounts (benchmark_results/summaries/miscount_attribution_2026-09-19.md).
ANEWDSC_FLAGS = {"anewdsc": "", "anewdsc_i0": "-i 0"}
# KILL_SLACK_S (2026-09-19, campaign 2 only): every arm is killed at cap + KILL_SLACK_S wall and a
# rep counts as completed iff its SELF-REPORTED solve time is <= cap. Before this, IsaRRI and
# anewdsc were killed at cap + 15 s but the in-process competitors, CGAL and Sage at exactly cap
# wall, so process start-up (Sage: ~2-4 s) and input parsing ate into their cap and not ours.
KILL_SLACK_S = 15
REP_MAJOR = False
STOP_AFTER_TIMEOUTS = 2   # campaign 2: --stop-after-timeouts (rep-major only)

# ---- the eight "ours" arms (PLAN §4 D5) ------------------------------------------------
# Both exports define the IDENTICAL five entry symbols, so they cannot be linked into one
# binary -- hence two, each traceable to a sha-checked archived bundle. Headers are identical
# pre/post and all five entries share one 12-arg signature, so ONE source serves both.
SUITE_BENCH_POST = f"{HARNESS}/build/suite_v2_bench_post"   # <- post-vcap-removal b72a73ad (PRE-E1; the adaptive_pre arm)
SUITE_BENCH_E1 = f"{HARNESS}/build/suite_v2_bench_e1"       # <- e1-prune-2026-08-10 f1180401 (the 5 post-E1 arms)
SUITE_BENCH_PRE = f"{HARNESS}/build/suite_v2_bench_pre"     # <- pre-vcap-removal  cf20ce84 (vcap A/B, retired)
SUITE_BENCH_SHIP = f"{HARNESS}/build/suite_v2_bench_ship"   # <- shipped df37bd98 2026-09-03 (R+E3+L3+D8+track_D, the AND flagship)

# ---- the all-competitors CAMPAIGN arms (docs/THESIS_CAMPAIGN_PLAN.md, 2026-09-12) ----------
# Named `allcomp_*`, NOT suite_v2: that name is retired from everything this campaign touches.
# Built by scripts/build-allcomp-bench.sh <l4|ship>. Two binaries because both exports define
# the SAME entry symbols and cannot be linked into one.
# 🔴 Any new binary name here must also be in bench-guard.sh's SOLVER_RE, or --strict/--stop
#    cannot see the process.
ALLCOMP_L4 = f"{HARNESS}/build/allcomp_bench_l4"       # <- the post-L4 export (thesis arm)
ALLCOMP_SHIP = f"{HARNESS}/build/allcomp_bench_ship"   # <- f3f96e19 L1+L2m (the A/B control)

# Reporting name -> the harness entry table's (legacy) name. The table in suite_v2_bench.cpp is
# proven glue and is deliberately NOT renamed; we translate here so the CSV reads clearly.
ENTRY_ALIAS = {"adaptive": "hybrid", "bail": "bail", "newton": "newton",
               "truncate": "dense", "bisection": "credit",
               "powsub": "powsub", "adaptive_ship": "hybrid",
               "powsub_l4": "powsub", "powsub_ship": "powsub"}
OURS_POST = ["adaptive", "bail", "newton", "truncate", "bisection"]
# Only these three reach a function that vcap removal changed -- verified by call-graph
# reachability over the two exports (PLAN §4): truncate/bisection are bit-identical, so a pre
# arm for them would measure the same machine code twice.
OURS_PRE = ["adaptive_pre", "bail_pre", "newton_pre"]
# Shipped-artifact arms (AND rerun, 2026-09-05): powsub is the flagship (E1+R+E3+L3+D8+track_D)
# and adaptive_ship is the drift control — same hybrid entry as adaptive but on the shipped
# binary, so the record run's sage/anewdsc cells can be tested for transferability without
# silently changing what the historical arm labels measure (handoff §1, docs/memory/...).
# lowdeg is available in the C++ binary (entry "lowdeg") but not wired as a python arm yet.
OURS_SHIP = ["powsub", "adaptive_ship"]
# The campaign panel: the SAME flagship entry on two artifacts, so the run yields the thesis
# ranking AND L4's ship gate G-e from one interleaved pass (THESIS_CAMPAIGN_PLAN.md §3).
OURS_CAMPAIGN = ["powsub_l4", "powsub_ship"]
# The thesis campaign panel (THESIS_CAMPAIGN_PLAN.md §2, 9 arms): the two campaign ours
# arms + the 7 in-scope competitors (arb out, decided 2026-08-06). Selected ONLY via
# --campaign; RECORD_SOLVERS is unchanged so every archived panel keeps its meaning.
# The 2026-09-12 campaign's panel, kept as run (z3 = isolate_roots, sage = real_root_intervals,
# pari = polrootsreal, libpoly = count+isolate). Superseded by --campaign2 (CAMPAIGN2_SOLVERS).
CAMPAIGN_SOLVERS = OURS_CAMPAIGN + ["z3", "msolve", "libpoly", "cgal", "pari", "sage",
                                    "anewdsc"]
CAMPAIGN = False  # set by main() from --campaign


def run_ours(c, solver, cap, reps):
    """Dispatch one of the ours arms to the correct per-export binary.
    adaptive_pre is the PRE-E1 baseline (post-vcap-removal b72a73ad): the E1 prune
    (e1-prune-2026-08-10) is a one-branch wrapper over that body, so the two arms differ
    ONLY by the E1 prune -- the AND-track A/B. The other pre arms (bail_pre, newton_pre)
    keep the old pre-vcap binary and are excluded from the AND panel at launch.
    powsub/adaptive_ship/lowdeg are the shipped-artifact arms (df37bd98, 2026-09-03)."""
    if solver in OURS_CAMPAIGN:
        # all-competitors campaign: one entry (powsub), two artifacts, two binaries.
        entry = ENTRY_ALIAS[solver]
        binary = ALLCOMP_L4 if solver == "powsub_l4" else ALLCOMP_SHIP
    elif solver in OURS_SHIP:
        # shipped binary — adaptive_ship is hybrid on the shipped export, powsub is the flagship
        entry = ENTRY_ALIAS[solver]
        binary = SUITE_BENCH_SHIP
    else:
        pre = solver.endswith("_pre")
        entry = ENTRY_ALIAS[solver[:-4] if pre else solver]
        if solver == "adaptive_pre":
            binary = SUITE_BENCH_POST          # post-vcap-removal == pre-E1
        elif pre:
            binary = SUITE_BENCH_PRE
        else:
            binary = SUITE_BENCH_E1            # the 5 post-E1 arms
    if FULL_REPS:
        # every rep gets its own invocation; min over COMPLETED reps; TIMEOUT iff none completed.
        best = None
        errs = []
        to_seen = False
        for i in range(max(1, reps)):
            with open(coeffs_path(c)) as fh:
                rc, out, err, to = _run([binary, "--solve-stdin", c["name"], entry, "1", str(cap)],
                                        timeout=cap + 15, stdin=fh)
            if to:
                to_seen = True
                print(f"    {c['name']}/{solver} rep{i+1} TIMEOUT", file=sys.stderr)
                if PREFLIGHT:
                    _after_timeout(f"row {c['name']}/{solver} after rep{i+1} timeout")
                continue
            if rc != 0:
                errs.append("ERROR:" + _errsnip(err))
                print(f"    {c['name']}/{solver} rep{i+1} ERROR: "
                      f"{err.strip()[:120]!r}", file=sys.stderr)
                continue
            r = type("R", (), {"stdout": out, "stderr": err})()
            try:
                line = [l for l in r.stdout.strip().splitlines()
                        if l.startswith(c["name"] + ",")][-1]
                parts = line.split(",")
                roots = int(parts[1].split("=")[1])
                ms = float(parts[2].split("=")[1])
                if ms < 0:                       # harness fork-deadline timeout marker
                    to_seen = True
                    print(f"    {c['name']}/{solver} rep{i+1} TIMEOUT", file=sys.stderr)
                    continue
                print(f"    {c['name']}/{solver} rep{i+1} OK roots={roots} {ms:.3f}ms",
                      file=sys.stderr)
                if best is None or ms < best[1]:
                    best = (roots, ms, "OK")
            except Exception as e:
                errs.append(f"PARSE_ERROR:{e}")
                print(f"    {c['name']}/{solver} rep{i+1} PARSE_ERROR: {e}", file=sys.stderr)
                continue
        if best is not None:
            return best
        if to_seen:
            return (-1, cap * 1000, "TIMEOUT")
        return (-1, -1, errs[0]) if errs else (-1, cap * 1000, "TIMEOUT")
    with open(coeffs_path(c)) as fh:
        rc, out, err, to = _run([binary, "--solve-stdin", c["name"], entry, str(reps), str(cap)],
                                timeout=cap + 15, stdin=fh)
    if to:
        return (-1, cap * 1000, "TIMEOUT")
    if rc != 0:
        return (-1, -1, "ERROR:" + _errsnip(err))
    r = type("R", (), {"stdout": out, "stderr": err})()
    try:
        line = [l for l in r.stdout.strip().splitlines() if l.startswith(c["name"] + ",")][-1]
        parts = line.split(",")
        roots = int(parts[1].split("=")[1])
        ms = float(parts[2].split("=")[1])
        if ms < 0:                       # harness reports its own fork-deadline timeout this way
            return (-1, cap * 1000, "TIMEOUT")
        return (roots, ms, "OK")
    except Exception as e:
        return (-1, -1, f"PARSE_ERROR:{e}:{r.stdout[:150]!r}")

# PLAN §4 Phase 1: bands are a property of the competitor field (D2 -- ours is NOT run here).
# The four below are each fastest somewhere in SUITE §4/§6, so between them they define every
# band. z3/arb are the binding constraint on B1 ("every solver completes") and nothing else, so
# they run on B1 only. cgal/libpoly are neither -- not run in calibration.
CALIB_ALL_BANDS = ["msolve", "anewdsc", "pari", "sage"]
CALIB_B1_EXTRA = ["z3", "arb"]
COMPETITORS = ["z3", "msolve", "libpoly", "arb", "cgal", "pari", "sage", "anewdsc"]
RECORD_SOLVERS = OURS_POST + OURS_PRE + OURS_SHIP + COMPETITORS   # 10 ours + 8 competitors = 18 (ship arms are the AND flagship)
# Families where band is NOT monotone in hardness — D4 ladder skip is unsound there.
# 2026-09-14 AMENDMENT (thesis campaign, mid-AND-leg): set EMPTIED — D4 enabled on the
# random families. The 2026-09-05 lt1 inversion (B5 42.9s then B6 55ms) is solve-TIME
# wiggle, but D4 arms only on FAILURE and needs only FRONTIER monotonicity
# (no completion above a failed band), which holds 48/48 (solver,family,table) ladders:
# 18/18 campaign random ladders + 30/30 prior-record random ladders, 0 violations.
# PAR2-neutral by construction (SKIP and TIMEOUT both charge 2C). Prior rows unaffected.
NONMONOTONIC_FAMILIES = set()
EXCLUDE = set()   # set by main() from --exclude-solver
FULL_REPS = False  # set by main() from --full-reps: every rep runs (no first-rep timeout abort);
#                   cell = min over COMPLETED reps; TIMEOUT only if NO rep completed.
PREFLIGHT = True   # set by main(): strict bench-guard check before startup, each row, and
#                   after each rep timeout -- a leak may not run on into the next measurement.

CASE_RE = re.compile(
    r'^\s*\{\s*(\d+)\s*,\s*(\d+)\s*,\s*"([^"]+)"\s*,\s*(\d+)\s*,\s*(-?\d+)\s*,'
    r'[^,]+,\s*(-?\d+)\s*,\s*(-?\d+)\s*,\s*(-?\d+)\s*,\s*"([^"]*)"')


def load_cases():
    """Parse final_suite_cases.hpp -> the 125 rows, family-major / band ascending."""
    cases = []
    for line in open(CASES_HPP):
        m = CASE_RE.match(line)
        if not m:
            continue
        cid, band, fam, deg, roots = int(m.group(1)), int(m.group(2)), m.group(3), \
            int(m.group(4)), int(m.group(5))
        cases.append(dict(id=cid, band=band, family=fam, degree=deg, oracle=roots,
                          desc=m.group(9), name=f"case_{cid}_{fam}", table=""))
    cases.sort(key=lambda c: (c["family"], int(c["table"] or 0), c["band"]))
    return cases


def coeffs_path(c):
    return f"{COEFFS}/{c['name']}.txt"


def load_table(path):
    """Load a campaign wave / final table from JSON (CALIBRATION_RUNBOOK_2026-08-04).

    The record driver normally reads the static 135-row final_suite_cases.hpp. The
    calibration campaign needs ARBITRARY levels (free parameters for the 5 ours families,
    e.g. kcluPure at K=64, tau=4096, which exists in no .hpp row), so the orchestrator
    writes the wave as JSON and we consume it here. Field shape mirrors load_cases():
    name, id, band, family, degree, desc (the params string), oracle.
    """
    with open(path) as fh:
        raw = json.load(fh)
    cases = []
    for r in raw:
        ov = r.get("oracle", -1)
        if not isinstance(ov, int):      # "PENDING" (AND-track guarded rows) -> -1, the
            ov = -1                      # suite's "no oracle" convention (timing-only rows)
        cases.append(dict(id=int(r["id"]), band=int(r["band"]), family=r["family"],
                          degree=int(r["degree"]), oracle=ov,
                          desc=r.get("desc", r.get("params", "")), name=r["name"],
                          table=str(r.get("table", ""))))
    cases.sort(key=lambda c: (c["family"], int(c["table"] or 0), c["band"]))
    return cases


def _errsnip(msg, n=90):
    """An ERROR string that can still be CLASSIFIED.

    `msg.strip()[:150]` keeps the HEAD of a Python traceback, which is
    "Traceback (most recent call last): File ..." — i.e. exactly the part that is identical for
    every failure — and throws away the LAST line, which is the exception type.  The campaign's
    2026-09-12 MPSolve leg recorded one sage ERROR whose class (the documented sage-internal
    RecursionError in `real_roots.pyx`) could only be recovered by reading the .sage.py by hand.
    "ERROR rows are OURS until traced" needs the type in the row.
    """
    t = " ".join(msg.strip().split())
    if len(t) <= 2 * n:
        return t
    return t[:n] + " ... " + t[-n:]

def _parse(out, name, idx_roots=2, idx_ms=3):
    parts = out.strip().split(",")
    return int(parts[idx_roots].split("=")[1]), float(parts[idx_ms].split("=")[1]), "OK"


def run_inprocess(c, solver, cap, reps):
    if FULL_REPS:
        best = None
        errs = []
        to_seen = False
        for i in range(max(1, reps)):
            with open(coeffs_path(c)) as fh:
                rc, out, err, to = _run([INPROC_BIN.get(solver, ALL_ROOTS_BIN),
                                         "--solve-stdin", c["name"], solver, "1"],
                                        timeout=cap, stdin=fh)
            if to:
                to_seen = True
                print(f"    {c['name']}/{solver} rep{i+1} TIMEOUT", file=sys.stderr)
                if PREFLIGHT:
                    _after_timeout(f"row {c['name']}/{solver} after rep{i+1} timeout")
                continue
            if rc != 0:
                errs.append("ERROR:" + _errsnip(err))
                print(f"    {c['name']}/{solver} rep{i+1} ERROR: "
                      f"{err.strip()[:120]!r}", file=sys.stderr)
                continue
            r = type("R", (), {"stdout": out, "stderr": err})()
            try:
                parts = r.stdout.strip().split(",")
                roots = int(parts[1].split("=")[1])
                ms = float(parts[2].split("=")[1])
                if ms < 0:
                    to_seen = True
                    print(f"    {c['name']}/{solver} rep{i+1} TIMEOUT", file=sys.stderr)
                    continue
                print(f"    {c['name']}/{solver} rep{i+1} OK roots={roots} {ms:.3f}ms",
                      file=sys.stderr)
                if best is None or ms < best[1]:
                    best = (roots, ms, "OK")
            except Exception as e:
                errs.append(f"PARSE_ERROR:{e}")
                print(f"    {c['name']}/{solver} rep{i+1} PARSE_ERROR: {e}", file=sys.stderr)
                continue
        if best is not None:
            return best
        if to_seen:
            return (-1, cap * 1000, "TIMEOUT")
        return (-1, -1, errs[0]) if errs else (-1, cap * 1000, "TIMEOUT")
    t0 = time.time()
    with open(coeffs_path(c)) as fh:
        rc, out, err, to = _run([INPROC_BIN.get(solver, ALL_ROOTS_BIN), "--solve-stdin", c["name"],
                                 solver, str(reps)],
                                timeout=cap, stdin=fh)
    if to:
        return (-1, (time.time() - t0) * 1000, "TIMEOUT")
    if rc != 0:
        return (-1, -1, "ERROR:" + _errsnip(err))
    r = type("R", (), {"stdout": out, "stderr": err})()
    try:
        parts = r.stdout.strip().split(",")
        return int(parts[1].split("=")[1]), float(parts[2].split("=")[1]), "OK"
    except Exception as e:
        return (-1, -1, f"PARSE_ERROR:{e}:{r.stdout[:150]!r}")


def run_cgal(c, cap, reps):
    # reps added 2026-08-05 (audit): the record protocol is min-of-3 for ALL 16 arms
    # (FINAL_BENCHMARK_PLAN.md line 13); this wrapper ignored reps until now. Semantics match
    # the suite harness: reps run sequentially, ANY rep over the cap marks the whole arm
    # TIMEOUT; else ms = min over reps. Deterministic solver -> roots identical across reps.
    best = None
    errs = []
    to_seen = False
    for i in range(max(1, reps)):
        with open(coeffs_path(c)) as fh:
            rc, out, err, to = _run([CGAL_BIN, "stdin", c["name"]], timeout=cap, stdin=fh)
        if to:
            if not FULL_REPS:
                return (-1, cap * 1000, "TIMEOUT")
            to_seen = True
            print(f"    {c['name']}/cgal rep{i+1} TIMEOUT", file=sys.stderr)
            if PREFLIGHT:
                _after_timeout(f"row {c['name']}/cgal after rep{i+1} timeout")
            continue
        if rc != 0:
            msg = "ERROR:" + _errsnip(err)
            if not FULL_REPS:
                return (-1, -1, msg)
            errs.append(msg)
            continue
        r = type("R", (), {"stdout": out, "stderr": err})()
        try:
            roots, ms, status = _parse(r.stdout, c["name"])
        except Exception as e:
            msg = f"PARSE_ERROR:{e}:{r.stdout[:150]!r}"
            if not FULL_REPS:
                return (-1, -1, msg)
            errs.append(msg)
            continue
        if FULL_REPS:
            print(f"    {c['name']}/cgal rep{i+1} OK roots={roots} {ms:.3f}ms", file=sys.stderr)
        best = (roots, ms, status) if best is None or ms < best[1] else best
    if best is None:
        if to_seen:
            return (-1, cap * 1000, "TIMEOUT")
        return (-1, -1, errs[0]) if errs else (-1, cap * 1000, "TIMEOUT")
    return best


# 🔴 2026-08-01: the 2026-07-21 run invoked gp with a FIXED 2 GB stack and no `parisizemax`, so
# every pari row that needed more died with "the PARI stack overflows" and an empty stdout --
# recorded as PARSE_ERROR, i.e. as a SOLVER FAILURE. It is not one; it is our misconfiguration.
# Verified on case_67_denseM1: gp -s 2000000000 overflows in seconds; with parisizemax set it
# runs past 120 s instead. So the honest status for those rows is TIMEOUT, never ERROR -- which
# also matters for D4, where a TIMEOUT correctly arms the family skip and a crash correctly
# does not. Any residual overflow is classified explicitly rather than left to look like a crash.
# Keep the ORIGINAL 2 GB initial stack and let parisizemax raise the ceiling. Measured on a
# quiesced machine, case_8_chebyshevT d512, 3 reps each: without parisizemax 469/469/470 ms,
# with it 470/470/469 ms -- the setting is FREE. (An earlier reading suggesting parisizemax cost
# ~1.5x was an artefact of orphaned benchmark processes, not of the setting; see PARI_SIZEMAX
# note in FINAL_BENCHMARK_PLAN.md §4b.)
PARI_STACK = 2_000_000_000     # initial, as in the 2026-07-21 run
PARI_SIZEMAX = 8_000_000_000   # ceiling, grew 6 GB -> 8 GB 2026-08-04 (universal cap, user decision)


def run_pari(c, cap, reps):
    # reps added 2026-08-05 (audit) — see run_cgal note; same min-of-reps semantics.
    coeffs = open(coeffs_path(c)).read().strip()
    # parisizemax MUST be its own line -- appended to the giant coeffs line it is silently
    # ignored (measured: gp then exits 0 in 0.0 s having done nothing).
    cmd = (f'default(parisizemax, {PARI_SIZEMAX});\n'
           f'coeffs=[{coeffs}]; casename="{c["name"]}"; read("{PARI_SCRIPT}")\n')
    best = None
    errs = []
    to_seen = False
    for i in range(max(1, reps)):
        rc, out, err, to = _run(["gp", "-q", "-s", str(PARI_STACK)], timeout=cap,
                                text_input=cmd, cwd=HARNESS)
        if to:
            if not FULL_REPS:
                return (-1, cap * 1000, "TIMEOUT")
            to_seen = True
            print(f"    {c['name']}/pari rep{i+1} TIMEOUT", file=sys.stderr)
            if PREFLIGHT:
                _after_timeout(f"row {c['name']}/pari after rep{i+1} timeout")
            continue
        r = type("R", (), {"stdout": out, "stderr": err, "returncode": rc})()
        if "stack overflow" in r.stderr or "stack overflows" in r.stderr:
            msg = f"PARI_STACK_OVERFLOW(>{PARI_SIZEMAX // 10**9}GB)"
            if not FULL_REPS:
                return (-1, -1, msg)
            errs.append(msg)
            continue
        if r.returncode != 0:
            msg = "ERROR:" + _errsnip(r.stderr)
            if not FULL_REPS:
                return (-1, -1, msg)
            errs.append(msg)
            continue
        try:
            line = [l for l in r.stdout.strip().splitlines() if l.startswith(c["name"] + ",")][-1]
            roots, ms, status = _parse(line, c["name"])
        except Exception as e:
            msg = f"PARSE_ERROR:{e}:{r.stdout[:150]!r}"
            if not FULL_REPS:
                return (-1, -1, msg)
            errs.append(msg)
            continue
        if FULL_REPS:
            print(f"    {c['name']}/pari rep{i+1} OK roots={roots} {ms:.3f}ms", file=sys.stderr)
        best = (roots, ms, status) if best is None or ms < best[1] else best
    if best is None:
        if to_seen:
            return (-1, cap * 1000, "TIMEOUT")
        return (-1, -1, errs[0]) if errs else (-1, cap * 1000, "TIMEOUT")
    return best


def run_sage(c, cap, reps, script=None):
    # reps added 2026-08-05 (audit) — see run_cgal note; same min-of-reps semantics.
    # ms is the solver's SELF-reported time, so sage's per-rep startup cost stays out of it.
    best = None
    errs = []
    to_seen = False
    for i in range(max(1, reps)):
        rc, out, err, to = _run(["sage", script or SAGE_SCRIPT, c["name"], coeffs_path(c)],
                                timeout=cap)
        if to:
            if not FULL_REPS:
                return (-1, cap * 1000, "TIMEOUT")
            to_seen = True
            print(f"    {c['name']}/sage rep{i+1} TIMEOUT", file=sys.stderr)
            if PREFLIGHT:
                _after_timeout(f"row {c['name']}/sage after rep{i+1} timeout")
            continue
        if rc != 0:
            msg = "ERROR:" + _errsnip(err)
            if not FULL_REPS:
                return (-1, -1, msg)
            errs.append(msg)
            continue
        r = type("R", (), {"stdout": out, "stderr": err})()
        try:
            roots, ms, status = _parse(r.stdout.strip().splitlines()[-1], c["name"])
        except Exception as e:
            msg = f"PARSE_ERROR:{e}:{r.stdout[:150]!r}"
            if not FULL_REPS:
                return (-1, -1, msg)
            errs.append(msg)
            continue
        if FULL_REPS:
            print(f"    {c['name']}/sage rep{i+1} OK roots={roots} {ms:.3f}ms", file=sys.stderr)
        best = (roots, ms, status) if best is None or ms < best[1] else best
    if best is None:
        if to_seen:
            return (-1, cap * 1000, "TIMEOUT")
        return (-1, -1, errs[0]) if errs else (-1, cap * 1000, "TIMEOUT")
    return best


def run_anewdsc(c, cap, reps, solver="anewdsc"):
    if FULL_REPS:
        best = None
        errs = []
        to_seen = False
        for i in range(max(1, reps)):
            rc, sout, serr, to = _run(["python3", ANEWDSC_PY, "--solve", ANEWDSC_BIN, c["name"],
                                       coeffs_path(c), str(cap), "1", ANEWDSC_FLAGS[solver]],
                                      timeout=cap + 15)
            if to:
                to_seen = True
                print(f"    {c['name']}/{solver} rep{i+1} TIMEOUT", file=sys.stderr)
                if PREFLIGHT:
                    _after_timeout(f"row {c['name']}/{solver} after rep{i+1} timeout")
                continue
            if rc != 0:
                errs.append("ERROR:" + _errsnip(serr))
                continue
            out = sout.strip()
            if "TIMED_OUT" in out:
                to_seen = True
                print(f"    {c['name']}/{solver} rep{i+1} TIMEOUT", file=sys.stderr)
                if PREFLIGHT:
                    _after_timeout(f"row {c['name']}/{solver} after rep{i+1} timeout")
                continue
            try:
                roots, ms, status = _parse(out, c["name"])
            except Exception as e:
                errs.append(f"PARSE_ERROR:{e}:{out[:150]!r}")
                continue
            print(f"    {c['name']}/{solver} rep{i+1} OK roots={roots} {ms:.3f}ms", file=sys.stderr)
            if best is None or ms < best[1]:
                best = (roots, ms, status)
        if best is not None:
            return best
        if to_seen:
            return (-1, cap * 1000, "TIMEOUT")
        return (-1, -1, errs[0]) if errs else (-1, cap * 1000, "TIMEOUT")
    rc, sout, serr, to = _run(["python3", ANEWDSC_PY, "--solve", ANEWDSC_BIN, c["name"],
                               coeffs_path(c), str(cap), str(reps), ANEWDSC_FLAGS[solver]],
                              timeout=cap + 15)
    if to:
        return (-1, cap * 1000, "TIMEOUT")
    if rc != 0:
        return (-1, -1, "ERROR:" + _errsnip(serr))
    out = sout.strip()
    if "TIMED_OUT" in out:
        return (-1, cap * 1000, "TIMEOUT")
    try:
        return _parse(out, c["name"])
    except Exception as e:
        return (-1, -1, f"PARSE_ERROR:{e}:{out[:150]!r}")


def run_one(c, solver, cap, reps):
    if solver in OURS_POST or solver in OURS_PRE or solver in OURS_SHIP \
            or solver in OURS_CAMPAIGN:
        return run_ours(c, solver, cap, reps)
    if solver in INPROCESS:
        return run_inprocess(c, solver, cap, reps)
    return {"cgal": run_cgal, "pari": run_pari, "sage": run_sage,
            "sagesqf": lambda c_, cap_, reps_: run_sage(c_, cap_, reps_, script=SAGE_SQF_SCRIPT),
            "anewdsc": run_anewdsc,
            "anewdsc_i0": lambda c_, cap_, reps_: run_anewdsc(c_, cap_, reps_, solver="anewdsc_i0"),
            }[solver](c, cap, reps)


def run_rep_major(c, active, cap, reps, case_idx):
    """Campaign 2: run every active arm once per repetition, the arm order rotated per
    (case, rep), so no arm's repetitions run back to back and no arm is always first or
    last. Cell semantics are those of --full-reps: min over completed reps; TIMEOUT only if
    no rep completed and one timed out; otherwise the first error."""
    acc = {s: {"best": None, "errs": [], "to": False, "roots": set(), "n_to": 0} for s in active}
    n = len(active)
    for r in range(max(1, reps)):
        shift = (case_idx + r) % n if n else 0
        for s in active[shift:] + active[:shift]:
            # EARLY STOP (2026-09-19, user): once STOP_AFTER_TIMEOUTS reps of a cell have hit the
            # cap, the cell is finished -- its remaining reps are not run. Campaign 1: of 248 cells
            # whose rep 1 timed out, no later rep ever completed. MPSolve leg: 2; AND leg: 1.
            if acc[s]["n_to"] >= STOP_AFTER_TIMEOUTS:
                continue
            # uniform cap (KILL_SLACK_S note): kill late, judge on the solver's own solve time
            roots, ms, status = run_one(c, s, cap + KILL_SLACK_S, 1)
            if status == "OK" and ms > cap * 1000:
                print(f"    {c['name']}/{s} rep{r+1} over cap on solve time ({ms:.0f} ms) -> TIMEOUT",
                      file=sys.stderr)
                status = "TIMEOUT"
            a = acc[s]
            if status == "OK":
                a["roots"].add(roots)
                if a["best"] is None or ms < a["best"][1]:
                    a["best"] = (roots, ms, "OK")
            elif status == "TIMEOUT":
                a["to"] = True
                a["n_to"] += 1
            else:
                a["errs"].append(status)
    out = {}
    for s, a in acc.items():
        if a["best"] is not None:
            if len(a["roots"]) > 1:      # counts differ between reps: never hide it
                print(f"WARNING {c['name']}/{s}: root counts differ across reps {sorted(a['roots'])}",
                      file=sys.stderr)
                out[s] = (-1, -1, "ERROR:NONDETERMINISTIC_COUNT" +
                          "|".join(map(str, sorted(a["roots"]))))
            else:
                out[s] = a["best"]
        elif a["to"]:
            out[s] = (-1, cap * 1000, "TIMEOUT")
        else:
            out[s] = (-1, -1, a["errs"][0] if a["errs"] else "ERROR:NO_RESULT")
    return out


def solvers_for(case, mode):
    if mode == "record":
        if ONLY_SOLVERS:
            return list(ONLY_SOLVERS)
        if CAMPAIGN2:
            return [s for s in CAMPAIGN2_SOLVERS if s not in EXCLUDE]
        if CAMPAIGN:
            return [s for s in CAMPAIGN_SOLVERS if s not in EXCLUDE]
        return [s for s in RECORD_SOLVERS if s not in EXCLUDE]
    return CALIB_ALL_BANDS + (CALIB_B1_EXTRA if case["band"] == 1 else [])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["calibrate", "record"], required=True)
    ap.add_argument("--cap", type=int, default=150)
    ap.add_argument("--reps", type=int, default=1)
    ap.add_argument("--out", default=None)
    ap.add_argument("--coeffs-dir", default=None,
                    help="coeffs dir override (default: benchmark_results/final_suite/coeffs)")
    ap.add_argument("--exclude-solver", default="",
                    help="comma-separated solver names to drop from the panel (e.g. arb)")
    ap.add_argument("--only-family", default=None, help="comma-separated family filter")
    ap.add_argument("--table", default=None,
                    help="JSON case table (calibration wave) instead of the .hpp table")
    ap.add_argument("--force-dirty", action="store_true",
                    help="skip the bench-guard preflight (ACCEPTS CONTAMINATED TIMINGS)")
    ap.add_argument("--no-preflight", action="store_true",
                    help="disable the per-row and post-timeout strict preflight "
                    "(the LAUNCH preflight still blocks; use --force-dirty to skip that too)")
    ap.add_argument("--full-reps", action="store_true",
                      help="run ALL reps even after a timeout; cell = min over completed reps, "
                      "TIMEOUT only if no rep completed")
    ap.add_argument("--campaign", action="store_true",
                    help="thesis campaign panel (THESIS_CAMPAIGN_PLAN.md §2): powsub_l4 + "
                    "powsub_ship + the 7 competitors, instead of RECORD_SOLVERS")
    ap.add_argument("--campaign2", action="store_true",
                    help="thesis campaign 2 panel (docs/THESIS_CAMPAIGN2_PLAN.md): IsaRRI + 7 competitors, "
                    "each on the same task; implies --rep-major")
    ap.add_argument("--rep-major", action="store_true",
                    help="run each rep of every arm before the next rep, arm order rotated per "
                    "(case, rep)")
    ap.add_argument("--stop-after-timeouts", type=int, default=2,
                    help="rep-major: a cell is finished once this many of its reps hit the cap "
                    "(campaign 2: MPSolve 2, AND 1)")
    ap.add_argument("--only-solvers", default="",
                    help="comma-separated panel override (e.g. z3sqf): run exactly these arms")
    args = ap.parse_args()
    global COEFFS, EXCLUDE, FULL_REPS, PREFLIGHT, CAMPAIGN, ONLY_SOLVERS, CAMPAIGN2, REP_MAJOR, GUARD_LOG
    global STOP_AFTER_TIMEOUTS
    CAMPAIGN2 = args.campaign2
    REP_MAJOR = args.rep_major or args.campaign2
    if CAMPAIGN2 and not args.full_reps:
        sys.exit("--campaign2 requires --full-reps")
    ONLY_SOLVERS = [s for s in args.only_solvers.split(",") if s]
    STOP_AFTER_TIMEOUTS = max(1, args.stop_after_timeouts)
    if args.coeffs_dir:
        COEFFS = args.coeffs_dir
    EXCLUDE = set(s for s in args.exclude_solver.split(",") if s)
    FULL_REPS = args.full_reps
    CAMPAIGN = args.campaign
    PREFLIGHT = not (args.force_dirty or args.no_preflight)
    if CAMPAIGN:
        print(f"# campaign panel: {','.join(s for s in CAMPAIGN_SOLVERS if s not in EXCLUDE)}",
              file=sys.stderr)
    if args.mode == "record" and not CAMPAIGN and "arb" not in EXCLUDE:
        # the record protocol's panel is 15 arms (8 ours + 7 competitors, arb dropped at the
        # 15-arm calibration -- MPSOLVE_BENCH.md §1). The driver has no built-in default, so
        # an omitted --exclude-solver silently changes the panel: say it out loud.
        print("NOTE: 'arb' is in the panel (16 arms); the record protocol panel is 15 -- "
              "pass --exclude-solver arb to match it", file=sys.stderr)

    # see the _kill_own_group note at the top: never leave a solver child behind.
    # macOS has no setsid(1), so become our own process-group leader here instead -- then
    # `kill -- -<pgid>` reaches every solver child. Harmless if we already lead a group.
    try:
        os.setsid()
    except OSError:
        pass
    print(f"# driver pid={os.getpid()} pgid={os.getpgid(0)} -- "
          f"stop with: kill -- -{os.getpgid(0)}", file=sys.stderr)

    # MANDATORY PREFLIGHT. A contaminated benchmark does not look broken -- it looks like a
    # result -- so refuse to start rather than emit rows nobody can later tell apart from good
    # ones. Measured 2026-08-01: leaked solver workers inflated timings ~1.9x.
    # --strict added 2026-08-04: plain --check only flags orphaned *known solvers*; an
    # unrelated 99%-CPU process (another agent's job) passed it as clean. The difference is a
    # busy-process gate: --strict fails while a FOREIGN process burns >= 30% CPU right now
    # (the decaying load average was replaced by an actual-CPU check 2026-08-04 — a stale
    # average blocked the campaign while the machine was idle).
    # (docs/memory/bench-guard-check-is-not-a-quiet-machine.md).
    guard = GUARD
    if os.path.exists(guard) and not args.force_dirty:
        _preflight("launch")
    for s in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(s, _on_signal)

    out = args.out or f"{REPO}/benchmark_results/final_suite/{args.mode}_results.csv"
    GUARD_LOG = out + ".guard.tsv"   # campaign 2: foreign CPU seen at non-blocking checks, orphan reaps
    os.makedirs(os.path.dirname(out), exist_ok=True)

    cases = load_table(args.table) if args.table else load_cases()
    if args.only_family:
        keep = set(args.only_family.split(","))
        cases = [c for c in cases if c["family"] in keep]

    # resume: skip (case,solver) pairs already recorded
    done = set(); resumed_rows = []
    if os.path.exists(out):
        with open(out) as fh:
            for row in csv.DictReader(fh):
                done.add((row["case"], row.get("params", ""), row["solver"]))
                resumed_rows.append(row)
        print(f"# resuming: {len(done)} (case,params,solver) triples already recorded",
              file=sys.stderr)

    # D4(b): per (solver, family, table), the lowest band at which that solver timed out
    timed_out_at = {}
    # D8: per (family, band) the winning time, and per (family, solver, band) that solver's time.
    # Used to eliminate a solver from B3+ once it has lost B1 AND B2 without improving.
    band_best = {}          # (family, band) -> best ms
    solver_at = {}          # (family, solver, band) -> ms
    eliminated = set()      # (family, solver)
    # Ladder state must be resolved against the CURRENT case table, never the CSV's band
    # column: a re-ladder re-ranks bands (AND grid 2026-08-10: all 295 rows were flat
    # band=1, re-encoded to per-(family,table) ranks 1..N). Seeding from the stale CSV
    # band would arm the D4 skip at the wrong level.
    case_by_name = {c["name"]: c for c in cases}
    # SEED from resumed rows. Without this a resumed run loses its D7 best-so-far and its D8
    # B1/B2 ratios, silently degrading to the un-optimised behaviour on every family already
    # touched -- the optimisation would appear to work while doing nothing.
    for r in resumed_rows:
        if r["status"] != "OK":
            continue
        f, b, sv, ms = r["family"], int(r["band"]), r["solver"], float(r["ms"])
        cc = case_by_name.get(r["case"])
        if cc is not None:
            f, b = cc["family"], cc["band"]
        if b in (1, 2):
            solver_at[(f, sv, b)] = min(ms, solver_at.get((f, sv, b), ms))
            k = (f, b)
            if k not in band_best or ms < band_best[k]:
                band_best[k] = ms
    for r in resumed_rows:                    # D4 skip state must survive a resume too
        # any FAILURE arms (TIMEOUT, ERROR:*, PARSE_ERROR, PARI_STACK_OVERFLOW) -- mirror of
        # the in-run arm at D4(d),(e); SKIPPED/ELIMINATED/SLOWER_THAN_BEST rows never seed
        if r["status"] != "OK" and not r["status"].startswith(
                ("SKIPPED", "ELIMINATED", "SLOWER")):
            cc = case_by_name.get(r["case"])
            # D4 disabled for non-monotone families — must not seed their skip state on resume either
            fam = cc["family"] if cc is not None else r["family"]
            if fam in NONMONOTONIC_FAMILIES:
                continue
            key = (r["solver"], r["family"], "")
            if cc is not None:
                key = (r["solver"], cc["family"], cc["table"])
            timed_out_at.setdefault(key, cc["band"] if cc is not None else int(r["band"]))

    new = os.path.getsize(out) == 0 if os.path.exists(out) else True
    fh = open(out, "a", newline="")
    w = csv.writer(fh)
    if new:
        # `params` is part of the RESUME KEY, not decoration: case NAMES are stable across a
        # re-ladder while their parameters change (kcluMig id 96 went n32k2t128 -> n64k8t512 on
        # 2026-08-01). Keying on the name alone would silently reuse measurements taken on a
        # different polynomial. Verified against the .poly cache headers before reuse.
        w.writerow(["case", "id", "band", "family", "degree", "params", "oracle", "solver",
                    "roots", "ms", "status"])
        fh.flush()

    t_start = time.time()
    n_to = n_skip = n_cut = n_elim = 0
    wins = collections.Counter()          # which solver is fastest, learned as we go
    for i, c in enumerate(cases):
        counts = {}
        # D7 BEST-SO-FAR CAPPING (calibration only, B2-B5 only). Measured 2026-08-01: 41% of
        # calibration solver-time is spent on solvers that CANNOT define the band, because a
        # band is the MINIMUM over competitors -- once one solver finishes in T, nothing slower
        # than T matters. So cap each subsequent solver at the running best.
        #   - RECORD MODE IS EXEMPT: it needs every solver's true time, not the minimum.
        #   - B1 IS EXEMPT: B1 asks "does EVERY solver complete?" (feasibility), not "who is
        #     fastest". Capping there would destroy exactly the fact B1 exists to establish.
        #     No loss: B1 rows are fast by definition.
        # Solvers are ordered fastest-first by observed wins so the cap tightens sooner.
        order = solvers_for(c, args.mode)
        if not REP_MAJOR:
            order = sorted(order, key=lambda s: -wins[s])
        if args.mode == "record" and not REP_MAJOR:
            # Rotate the arm order per case so no arm is always first/last
            # (SMT-leg precedent, 2026-09-12: fastest-first alone systematises
            # order effects such as cold-vs-warm cache). Ordering only: cell
            # values and resume keys are unaffected.
            rot = i % len(order)
            order = order[rot:] + order[:rot]
        # D7 capping starts at B3: B1 is the feasibility row, and B2 must be measured in full
        # because D8 needs each solver's TRUE B1 and B2 times to compute its scaling ratio.
        # Cost of exempting B2 is trivial (B2 is 0.1-1 s by definition); it unlocks D8 on the
        # expensive bands B3-B5.
        use_cut = (args.mode == "calibrate" and c["band"] > 2)
        best_ms = None
        best_solver = None
        if PREFLIGHT:
            if not CAMPAIGN2:
                _preflight(f"case {c['name']} (band {c['band']})")
            elif c["family"] not in GUARD_SEEN_FAMILIES:
                GUARD_SEEN_FAMILIES.add(c["family"])
                t_g = time.time()
                _preflight(f"first case of family {c['family']}: {c['name']}")
                print(f"    guard: blocking check for family {c['family']} passed after "
                      f"{time.time() - t_g:.1f}s", file=sys.stderr)
            else:
                _note_foreign(f"case {c['name']}")
        rm_results = {}
        if REP_MAJOR:
            active = [s for s in order if (c["name"], c["desc"], s) not in done
                      and not (timed_out_at.get((s, c["family"], c["table"])) is not None
                               and c["band"] > timed_out_at[(s, c["family"], c["table"])]
                               and c["family"] not in NONMONOTONIC_FAMILIES)]
            rm_results = run_rep_major(c, active, args.cap, args.reps, i)
        for solver in order:
            if (c["name"], c["desc"], solver) in done:
                continue
            lo = timed_out_at.get((solver, c["family"], c["table"]))
            if lo is not None and c["band"] > lo and c["family"] not in NONMONOTONIC_FAMILIES:          # D4(b),(e) — disabled for non-monotone families
                roots, ms, status = -1, -1, f"SKIPPED(>=B{lo})"
                n_skip += 1
            elif (c["family"], solver) in eliminated and c["band"] > 2:   # D8
                roots, ms, status = -1, -1, "ELIMINATED(lost_B1+B2_no_better_scaling)"
                n_elim += 1
            else:
                eff = args.cap
                if use_cut and best_ms is not None:
                    eff = max(1, min(args.cap, int(best_ms / 1000.0) + 1))
                roots, ms, status = (rm_results[solver] if REP_MAJOR
                                     else run_one(c, solver, eff, args.reps))
                if status == "TIMEOUT" and eff < args.cap:
                    # NOT a real timeout -- it merely lost the race. It must never arm the D4
                    # family skip (D4(d)), and must never be read as a completion.
                    ms, status = -1, f"SLOWER_THAN_BEST(>{eff}s)"
                    n_cut += 1
                elif status != "OK" and c["family"] not in NONMONOTONIC_FAMILIES:     # D4(d),(e): a REAL cap timeout OR any failure (crash,
                    timed_out_at.setdefault((solver, c["family"], c["table"]), c["band"])
                    # parse error, solver ERROR) arms the ladder skip -- a solver that fails on
                    # a lower band is not going to complete a harder one, so harder rows of the
                    # same family+table become SKIPPED (recorded non-completion, roots=-1).
                    # ⚠️ 2026-08-11: was TIMEOUT-only; the sage hermite_d1024 ERROR (RecursionError
                    # inside sage's real_roots) kept paying 3 reps x cap on every harder row.
                    if status == "TIMEOUT":
                        n_to += 1
                if status == "OK" and (best_ms is None or ms < best_ms):
                    best_ms, best_solver = ms, solver
                if status == "OK" and c["band"] in (1, 2):
                    solver_at[(c["family"], solver, c["band"])] = ms
            w.writerow([c["name"], c["id"], c["band"], c["family"], c["degree"], c["desc"],
                        c["oracle"], solver, roots, f"{ms:.4f}" if ms >= 0 else ms, status])
            fh.flush()
            if status == "OK":
                counts.setdefault(roots, []).append(solver)
        if best_solver is not None:
            wins[best_solver] += 1      # feeds the fastest-first ordering for later cases
        if best_ms is not None and c["band"] in (1, 2):
            band_best[(c["family"], c["band"])] = best_ms
        if c["band"] == 2:
            # D8 VERDICT (calibration only). A solver that lost BOTH B1 and B2 and did not
            # narrow the gap cannot overtake on harder rows, so it can never define a band.
            # Validated on the 2026-07-21 data: 32/32 such (solver,family) pairs never became
            # fastest on any harder row; 0 counter-examples. A solver that IMPROVED its ratio
            # (r2 < r1) is KEPT -- that is precisely the overtaking signal.
            w1 = band_best.get((c["family"], 1)); w2 = band_best.get((c["family"], 2))
            if args.mode == "calibrate" and w1 and w2:
                for sv in set(x[1] for x in solver_at if x[0] == c["family"]):
                    t1 = solver_at.get((c["family"], sv, 1)); t2 = solver_at.get((c["family"], sv, 2))
                    if t1 is None or t2 is None:
                        continue                       # never completed one of them: D4 covers it
                    if t1 <= w1 or t2 <= w2:
                        continue                       # won a band -> keep
                    if (t2 / w2) < (t1 / w1):
                        continue                       # closing the gap -> keep
                    eliminated.add((c["family"], sv))
        if len(counts) > 1 or (c["oracle"] >= 0 and any(root != c["oracle"] for root in counts)):
            # disagreement between solvers, OR an OK solver violating the oracle (catches a
            # lone miscounter when every other arm times out); oracle -1 = no analytic oracle
            print(f"WARNING root-count mismatch {c['name']} (oracle {c['oracle']}): {counts}",
                  file=sys.stderr)
        print(f"[{i+1}/{len(cases)}] {c['name']:28s} B{c['band']} "
              f"({(time.time()-t_start)/60:.1f} min, {n_to} timeouts, {n_skip} skipped, "
              f"{n_cut} cut-as-slower, {n_elim} eliminated)", file=sys.stderr)
    fh.close()
    print(f"DONE {(time.time()-t_start)/60:.1f} min -- {n_to} timeouts, {n_skip} skipped",
          file=sys.stderr)


if __name__ == "__main__":
    main()

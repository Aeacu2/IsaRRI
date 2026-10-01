#!/usr/bin/env python3
"""SMT-BENCH Phase 2 runner: 15-arm timing race on the fired instances' extracted A
polynomials (docs/SMT_BENCH.md §1.5 — protocol and per-arm invocations; §2 — oracle).

Workload: one subprocess per (instance, arm, rep); the process reads the instance's
.extracted/<instance>.apolys file (one dump-format poly per line, "A\t<deg>\t<c0>,...")
and isolates ALL of them IN-PROCESS (multi-poly drivers: suite_v2_bench --solve-stdin-multi,
all_roots_vs_competitors_bench --solve-stdin-multi, cgal stdin-multi, pari_solve_multi.gp,
sage_solve_multi.sage, anewdsc_bench.py --solve-multi, z3_isolate_timer --sum). Per-poly
process spawn would be infeasible (341K polys x 15 arms x 5 reps).

Per-poly rows: every driver additionally emits one "P\t<idx>\t<deg>\t<roots>\t<ms>" line
per polynomial (z3 reports ns); the runner writes them to results/phase2_run2_polys.tsv and
cross-checks that they sum to the instance row (mismatch -> ERROR row, no poly rows).

Protocol (pre-registered in docs/SMT_BENCH.md):
  * cap 1 s per (instance, arm, rep) -- the CLASSIFICATION threshold on the driver's
    SOLVE time (ms column), run1-style: subprocess.run(timeout=CAP_S + 15) kills only
    the truly stuck (run1's effective 165 s at cap 150; cells slower than the cap
    COMPLETE and are flagged ">cap" at report time, exactly like run1's "+26 >cap"
    sage cells at cap 1);
  * interpreter-startup fairness: sage's cell wall is ~1.8 s of startup, so its kill
    deadline is raised by SAGE_STARTUP_MS (measured min-of-cells, 2026-08-08). Its ms
    column is the driver-internal SOLVE time; startup never enters a reported time
    (run1 convention, verify.py check 6);
  * N = 5 interleaved reps: arms are rotated per rep so no arm always runs first/last;
  * sequential execution (one subprocess at a time): timings are load-sensitive, and the
    record protocol does not co-schedule arms;
  * z3's arm runs z3_isolate_timer --sum (in-engine sqf_isolate_roots, the exact function
    the NLSAT engine calls); its per-instance summed nroots IS the root-count oracle;
  * arb excluded; z3 in all_roots_vs_competitors_bench is NOT used (bound-free
    isolate_roots, not sqf_isolate_roots);
  * bench-guard.sh --check --strict before each rep block (drivers excluded by ancestry,
    so our own subprocesses never trip it);
  * caffeinate -dimsu -w <self> (PreventSystemSleep): macOS idle sleep pauses
    subprocess.run(timeout=) and perf_counter, inflating wall_ms by the sleep duration
    (2026-08-09 incident; ms/counts stay honest);
  * on timeout the whole process GROUP is killed (sage/anewdsc spawn children);
  * rows are flushed per completion -- wait on the artifact, never the wrapper's exit code.

Usage:
  python3 smt_bench_phase2.py [--limit N] [--only <inst-prefix>] [--resume]
"""
import argparse
import datetime
import hashlib
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
EXT = os.path.join(HERE, "extracted")
MANIFEST = os.path.join(EXT, "manifest.tsv")
OUTDIR = os.path.join(HERE, "results")
CAP_S = 1          # solve-time classification threshold (ms > CAP_S is ">cap", never a kill)
REPS = 5
# Subprocess kill deadline = CAP_S + 15 (run1-style grace) + per-arm interpreter-startup
# allowance. Sage's: measured min cell wall 1789.7 ms (2026-08-08), startup-dominated;
# 4.0 s keeps every run1-observed sage cell alive (max wall 18.6 s < 16 + 4.0). The ms
# column is the driver-internal SOLVE time; the allowance only prevents startup kills.
STARTUP_ALLOW_S = {"sage": 4.0, "sagesqf": 4.0}

HARNESS = os.path.join(REPO, "Dsc/export/c_harness")
SUITE_POST = os.path.join(HARNESS, "build/suite_v2_bench_post")
SUITE_PRE = os.path.join(HARNESS, "build/suite_v2_bench_pre")
# Thesis campaign arms (docs/THESIS_CAMPAIGN_PLAN.md §2): the SAME flagship entry
# (powsub) on two artifacts. Built by scripts/build-allcomp-bench.sh <l4|ship> from
# the same suite_v2_bench.cpp source, so --solve-stdin-multi works unchanged.
ALLCOMP_L4 = os.path.join(HARNESS, "build/allcomp_bench_l4")
ALLCOMP_SHIP = os.path.join(HARNESS, "build/allcomp_bench_ship")
ALL_ROOTS = os.path.join(HARNESS, "build/all_roots_vs_competitors_bench")
CGAL = os.path.join(HARNESS, "build/cgal_descartes_bench")
Z3_TIMER = os.path.join(HERE, "z3_isolate_timer")
PARI_MULTI = os.path.join(HARNESS, "pari_solve_multi.gp")
SAGE_MULTI = os.path.join(HARNESS, "sage_solve_multi.sage")
ANEWDSC_PY = os.path.join(HARNESS, "anewdsc_bench.py")
# Thesis campaign 2 (2026-09-18; docs/THESIS_CAMPAIGN2_PLAN.md): each competitor on the same task as
# IsaRRI (squarefree input, no squarefree preprocessing, isolation only).
SAGE_MULTI_SQF = os.path.join(HARNESS, "sage_solve_multi_sqf.sage")
PARI_TIMER = os.path.join(HARNESS, "build/pari_timer")
LIBPOLY_NOSQF = os.path.join(HARNESS, "build/libpoly_nosqf_timer")
ANEWDSC_BIN = os.path.expanduser("~/Downloads/test_descartes_osx")
GUARD = os.path.join(REPO, "scripts/bench-guard.sh")

# Reporting name -> suite_v2_bench entry (same table as scripts/final-suite-run.py).
ENTRY_ALIAS = {"adaptive": "hybrid", "bail": "bail", "newton": "newton",
               "truncate": "dense", "bisection": "credit",
               "powsub_l4": "powsub", "powsub_ship": "powsub"}
OURS = [("adaptive", SUITE_POST), ("bail", SUITE_POST), ("newton", SUITE_POST),
        ("truncate", SUITE_POST), ("bisection", SUITE_POST),
        ("adaptive_pre", SUITE_PRE), ("bail_pre", SUITE_PRE), ("newton_pre", SUITE_PRE)]
# Thesis campaign ours arms (THESIS_CAMPAIGN_PLAN.md §2). Selected ONLY via --campaign;
# OURS/ARMS are unchanged so the 15-arm panel keeps its meaning.
OURS_CAMPAIGN_SMT = [("powsub_l4", ALLCOMP_L4), ("powsub_ship", ALLCOMP_SHIP)]

COMPETITOR_ARMS = ["z3", "msolve", "libpoly", "cgal", "pari", "sage", "anewdsc"]
ARMS = [name for name, _ in OURS] + COMPETITOR_ARMS  # 15
CAMPAIGN_ARMS = [name for name, _ in OURS_CAMPAIGN_SMT] + COMPETITOR_ARMS  # 9
# z3 here is already z3_isolate_timer = sqf_isolate_roots (the call z3's own NLSAT makes).
# anewdsc_i0 (2026-09-19): anewdsc -S 1 -i 0 sensitivity arm (miscount_attribution_2026-09-19.md).
CAMPAIGN2_ARMS = ["powsub_l4", "msolve", "anewdsc", "anewdsc_i0", "sagesqf", "parisqf", "z3", "cgal",
                  "libpolysqf"]
CAMPAIGN = False  # set by main() from --campaign

# Matches both "hybrid_roots=4,hybrid_ms=0.03" (ours/msolve/libpoly) and plain
# "roots=4,ms=0.03" (cgal/pari/sage/anewdsc) -- the prefixed form contains the bare one.
_ROW_RE = re.compile(r"roots=(-?[0-9]+)")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()[:16]


def parse_poly_lines(out, arm):
    """Extract per-poly rows from driver stdout: lines "P\t<idx>\t<deg>\t<roots>\t<ms>"
    (z3: last field is ns). Returns list of (idx, deg, roots, ms) and the non-P lines."""
    rows, rest = [], []
    for line in out.splitlines():
        if line.startswith("P\t"):
            p = line.split("\t")
            if len(p) == 5:
                ms = float(p[4]) / 1e6 if arm == "z3" else float(p[4])
                rows.append((int(p[1]), int(p[2]), int(p[3]), ms))
                continue
        rest.append(line)
    return rows, rest


def run_one(instance, apolys, arm, rep, out_tsv, poly_tsv):
    """Run one (instance, arm, rep); append one TSV row + per-poly rows. Returns
    (status, roots, ms, polys). Per-poly rows are written BEFORE the instance row so a
    crash between the two leaves the instance row absent and --resume redoes the cell
    (duplicate poly rows are then visible to smt_bench_verify.py; a missing instance
    row would silently lose the poly rows instead)."""
    name = arm
    input_text = None
    ours_table = OURS + OURS_CAMPAIGN_SMT if CAMPAIGN else OURS
    ours_names = [n for n, _ in ours_table]
    if arm in ours_names:      # ours
        binary = dict(ours_table)[arm]
        cmd = [binary, "--solve-stdin-multi", instance, ENTRY_ALIAS[arm[:-4] if arm.endswith("_pre") else arm], str(CAP_S + 15)]
        stdin = open(apolys, "r")
    elif arm == "z3":
        cmd = [Z3_TIMER, "--sum", apolys]
        stdin = subprocess.DEVNULL
    elif arm in ("msolve", "libpoly"):
        cmd = [ALL_ROOTS, "--solve-stdin-multi", instance, arm]
        stdin = open(apolys, "r")
    elif arm == "cgal":
        cmd = [CGAL, "stdin-multi", instance]
        stdin = open(apolys, "r")
    elif arm == "pari":
        input_text = f'polysfile="{apolys}";casename="{instance}";read("{PARI_MULTI}")\n'
        cmd = ["gp", "-q"]
        stdin = None
    elif arm == "sage":
        cmd = ["sage", SAGE_MULTI, instance, apolys]
        stdin = subprocess.DEVNULL
    elif arm == "sagesqf":
        cmd = ["sage", SAGE_MULTI_SQF, instance, apolys]
        stdin = subprocess.DEVNULL
    elif arm == "parisqf":
        cmd = [PARI_TIMER, "--solve-stdin-multi", instance, arm]
        stdin = open(apolys, "r")
    elif arm == "libpolysqf":
        cmd = [LIBPOLY_NOSQF, "--solve-stdin-multi", instance, arm]
        stdin = open(apolys, "r")
    elif arm == "anewdsc_i0":
        cmd = ["python3", ANEWDSC_PY, "--solve-multi", ANEWDSC_BIN, instance, apolys, "120", "-i 0"]
        stdin = subprocess.DEVNULL
    else:  # anewdsc
        cmd = ["python3", ANEWDSC_PY, "--solve-multi", ANEWDSC_BIN, instance, apolys]
        stdin = subprocess.DEVNULL

    t0 = datetime.datetime.now(datetime.timezone.utc)
    kill_after_s = CAP_S + 15 + STARTUP_ALLOW_S.get(arm, 0.0)
    try:
        proc = subprocess.run(cmd, stdin=stdin, capture_output=True, text=True,
                              timeout=kill_after_s, start_new_session=True,
                              input=input_text)
        rc, out, err, to = proc.returncode, proc.stdout, proc.stderr, False
    except subprocess.TimeoutExpired as e:
        try:
            os.killpg(e.pid, 9)
        except Exception:
            pass
        rc, out, err, to = -1, "", str(e), True
    finally:
        try:
            if isinstance(stdin, object) and hasattr(stdin, "close"):
                stdin.close()
        except Exception:
            pass
    t1 = datetime.datetime.now(datetime.timezone.utc)
    wall_ms = (t1 - t0).total_seconds() * 1000.0

    if to:
        status, roots, ms, polys = "TIMEOUT", "NA", "NA", "NA"
    elif rc != 0:
        status, roots, ms, polys = "ERROR", "NA", "NA", "NA"
        err = err.strip()[:200].replace("\n", " ")
    else:
        poly_rows, rest = parse_poly_lines(out, arm)
        # z3 --sum prints "<roots>\t<ns>\t<npolys>" on its LAST line; parse that, not
        # _ROW_RE (which would match nothing in z3's output).
        if arm == "z3":
            parts = rest[-1].split("\t") if rest else []
            if len(parts) == 3:
                status, roots, ms, polys = ("OK", int(parts[0]),
                                            float(parts[1]) / 1e6, int(parts[2]))
            else:
                status, roots, ms, polys = "ERROR", "NA", "NA", "NA"
                err = f"z3 --sum malformed output {out.strip()[:100]!r}"
        else:
            m = _ROW_RE.search("\n".join(rest))
            if m:
                status, roots = "OK", int(m.group(1))
                mm = re.search(r"_?ms=([-0-9.eE+]+)", "\n".join(rest))
                pm = re.search(r",polys=([0-9]+)", "\n".join(rest))
                ms = float(mm.group(1)) if mm else "NA"
                polys = int(pm.group(1)) if pm else "NA"
            else:
                status, roots, ms, polys = "ERROR", "NA", "NA", "NA"
                err = f"unparseable output {out.strip()[:100]!r}"
        if status == "OK" and poly_rows:
            # Consistency: per-poly rows must sum exactly to the summary row.
            p_roots = sum(r[2] for r in poly_rows)
            p_ms = sum(r[3] for r in poly_rows)
            if polys != "NA" and len(poly_rows) != polys:
                status = "ERROR"
                err = f"poly-row count {len(poly_rows)} != summary polys {polys}"
            elif roots != "NA" and p_roots != roots:
                status = "ERROR"
                err = f"poly-row roots {p_roots} != summary roots {roots}"
            elif ms != "NA" and abs(p_ms - ms) > max(1e-6, 1e-3 * abs(ms)):
                status = "ERROR"
                err = f"poly-row ms {p_ms:.6f} != summary ms {ms}"
            else:
                with open(poly_tsv, "a") as f:
                    for idx, deg, r_, m_ in poly_rows:
                        f.write(f"{instance}\t{arm}\t{rep}\t{idx}\t{deg}\t{r_}\t{m_}\n")

    with open(out_tsv, "a") as f:
        f.write(f"{instance}\t{arm}\t{rep}\t{status}\t{roots}\t{ms}\t{polys}\t"
                f"{wall_ms:.1f}\t{rc}\t{err}\n")
    return status, roots, ms, polys


def preflight_strict(max_tries=12, wait_s=30):
    """bench-guard --check --strict; read its rc DIRECTLY (piping masks it).

    Transient macOS daemon spikes (trustd/ecosystemd burning >30% for seconds) trip
    --strict; the guard's own guidance is "stop it or wait". Wait-and-recheck (bounded)
    keeps the gate's teeth -- the campaign still ABORTS if foreign CPU persists -- while
    surviving a transient spike that would otherwise kill a multi-hour run at every
    instance boundary (observed 2026-08-08: 6 aborts in ~40 min, daemons 0% between).
    """
    for attempt in range(max_tries):
        r = subprocess.run([GUARD, "--check", "--strict"], capture_output=True, text=True)
        if r.returncode == 0:
            print(f"# bench-guard --check --strict: rc=0 OK (attempt {attempt + 1})")
            return True
        print(f"# bench-guard --check --strict: rc={r.returncode} (attempt {attempt + 1}/"
              f"{max_tries}); waiting {wait_s}s for foreign CPU to clear...")
        print(r.stdout)
        print(r.stderr)
        if attempt + 1 < max_tries:
            time.sleep(wait_s)
    return False


CORPUS = {}  # instance -> corpus (manifest column 2), the SMT-BENCH "family" for the guard policy


def preflight_blocking(where):
    """Campaign 2 (2026-09-19, user): wait until the strict check passes -- never abort. An abort
    cost a 600 s runner retry on top of the waits (preflight_strict gives up after 12 x 30 s)."""
    n = 0
    while True:
        r = subprocess.run([GUARD, "--check", "--strict"], capture_output=True, text=True)
        if r.returncode == 0:
            return
        n += 1
        if n == 1 or n % 6 == 0:
            print(f"# bench-guard strict rc={r.returncode} before {where}; waiting (10 s re-checks)\n{r.stdout}")
            sys.stdout.flush()
        time.sleep(10)


def note_foreign(where, log_path):
    """Non-blocking strict check: log foreign CPU to <out>.guard.tsv for later re-measurement."""
    r = subprocess.run([GUARD, "--check", "--strict"], capture_output=True, text=True)
    if r.returncode != 0:
        offenders = " | ".join(l.strip() for l in r.stdout.splitlines() if l.strip().startswith("pid="))
        with open(log_path, "a") as fh:
            fh.write(f"{time.strftime('%Y-%m-%dT%H:%M:%S')}\t{where}\t{offenders}\n")
        print(f"# guard: foreign CPU before {where} (logged, not waited on): {offenders[:150]}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--only", default="")
    ap.add_argument("--resume", action="store_true")
    ap.add_argument("--skip-guard", action="store_true")
    ap.add_argument("--campaign", action="store_true",
                    help="thesis campaign panel (THESIS_CAMPAIGN_PLAN.md §2): powsub_l4 + "
                    "powsub_ship + the 7 competitors, written to campaign_run1.tsv "
                    "(never phase2_run2.tsv)")
    ap.add_argument("--campaign2", action="store_true",
                    help="thesis campaign 2 panel (docs/THESIS_CAMPAIGN2_PLAN.md), written to "
                    "campaign2_run1.tsv")
    ap.add_argument("--outdir", default=None, help="write results here instead of results/ (smoke tests)")
    ap.add_argument("--no-caffeinate", action="store_true",
                    help="do not hold PreventSystemSleep (default: caffeinate -dimsu -w <self>)")
    args = ap.parse_args()
    global ARMS, CAMPAIGN
    CAMPAIGN = args.campaign or args.campaign2
    if args.campaign2:
        ARMS = CAMPAIGN2_ARMS
        print(f"# campaign2 panel: {','.join(ARMS)}", file=sys.stderr)
    elif CAMPAIGN:
        ARMS = CAMPAIGN_ARMS
        print(f"# campaign panel: {','.join(ARMS)}", file=sys.stderr)

    # macOS idle sleep pauses subprocess.run(timeout=) and perf_counter alike, inflating
    # wall_ms by the sleep duration (observed 2026-08-09: cells 900 s+ against a 16-20 s
    # deadline; ms/counts stayed honest). Hold the machine awake for the runner's life.
    if not args.no_caffeinate and sys.platform == "darwin":
        try:
            subprocess.Popen(["caffeinate", "-dimsu", "-w", str(os.getpid())])
        except FileNotFoundError:
            print("# caffeinate not found; system may sleep during the run", file=sys.stderr)

    global OUTDIR
    if args.outdir:
        OUTDIR = args.outdir
    os.makedirs(OUTDIR, exist_ok=True)
    stem = "campaign2_run1" if args.campaign2 else "campaign_run1" if CAMPAIGN else "phase2_run2"
    out_tsv = os.path.join(OUTDIR, stem + ".tsv")
    poly_tsv = os.path.join(OUTDIR, stem + "_polys.tsv")
    header = ("# instance\tarm\trep\tstatus\troots\tms\tpolys\twall_ms\trc\terr\n"
              "# cap_s=1 reps=5 oracle=z3 --sum nroots panel=" + ",".join(ARMS) + "\n"
              "# cap_s=1 is the solve-time CLASSIFICATION threshold (kill=cap+15+startup_allow, "
              "run1-style); sage startup allowance 4.0 s\n")
    poly_header = ("# instance\tarm\trep\tpoly\tdeg\troots\tms\n"
                   "# per-poly sidecar of phase2_run2.tsv; one row per isolated polynomial\n")

    instances = []
    with open(MANIFEST) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("instance"):
                continue
            parts = line.split("\t")
            inst, corpus = parts[0], parts[1]
            apolys = os.path.join(EXT, inst + ".apolys")
            if not os.path.exists(apolys):
                continue
            instances.append((inst, apolys))
            CORPUS[inst] = corpus
    if args.only:
        instances = [(i, a) for i, a in instances if i.startswith(args.only)]
    if args.limit:
        instances = instances[: args.limit]

    done = set()
    if args.resume and os.path.exists(out_tsv):
        with open(out_tsv) as f:
            for line in f:
                if line.startswith("#"):
                    continue
                parts = line.split("\t")
                if len(parts) >= 3:
                    done.add((parts[0], parts[1], parts[2]))

    print(f"# SMT-BENCH Phase 2: {len(instances)} instances, {len(ARMS)} arms x {REPS} reps, "
          f"cap {CAP_S}s, sequential")
    if not os.path.exists(out_tsv):
        with open(out_tsv, "w") as f:
            f.write(header)
    if not os.path.exists(poly_tsv):
        with open(poly_tsv, "w") as f:
            f.write(poly_header)

    # Provenance: binaries + guard + manifest sha256s, once.
    prov = [f"# start={datetime.datetime.now(datetime.timezone.utc).isoformat()}"]
    for p in ([SUITE_POST, SUITE_PRE, ALLCOMP_L4, ALLCOMP_SHIP, ALL_ROOTS, CGAL, Z3_TIMER,
               PARI_MULTI, SAGE_MULTI, ANEWDSC_PY, ANEWDSC_BIN, MANIFEST,
               SAGE_MULTI_SQF, PARI_TIMER, LIBPOLY_NOSQF]):
        if os.path.exists(p):
            prov.append(f"# sha16 {sha256(p)}  {os.path.relpath(p, REPO)}")
        else:
            prov.append(f"# MISSING {p}")
    with open(out_tsv, "a") as f:
        for line in prov:
            f.write(line + "\n")

    n_inst, n_rows, n_err = 0, 0, 0
    seen_corpora = set()
    for inst, apolys in instances:
        n_inst += 1
        if args.skip_guard:
            pass
        elif args.campaign2:
            # campaign-2 guard policy (final-suite-run.py GUARD_SEEN_FAMILIES note): block once per
            # corpus, otherwise check without waiting and log foreign CPU for re-measurement.
            corpus = CORPUS.get(inst, "?")
            if corpus not in seen_corpora:
                seen_corpora.add(corpus)
                preflight_blocking(f"first instance of corpus {corpus}: {inst}")
            else:
                note_foreign(f"instance {inst}", out_tsv + ".guard.tsv")
        elif not preflight_strict():
            print(f"# ABORT: bench-guard strict failed before {inst}", file=sys.stderr)
            return 2
        # Interleaved reps: rotate the arm order per (instance, rep) so no arm is
        # always first/last. The instance index folds into the shift: rep-only
        # rotation repeats one order across all instances per rep (and with 5
        # reps x 9 arms four arms never lead). Campaign fairness, 2026-09-13.
        for rep in range(1, REPS + 1):
            shift = (n_inst + rep - 1) % len(ARMS)
            rot = ARMS[shift:] + ARMS[:shift]
            for arm in rot:
                if (inst, arm, str(rep)) in done:
                    continue
                status, roots, ms, polys = run_one(inst, apolys, arm, rep, out_tsv, poly_tsv)
                n_rows += 1
                if status != "OK":
                    n_err += 1
                print(f"  [{n_inst}/{len(instances)}] {inst} {arm} rep{rep}: "
                      f"{status} roots={roots} ms={ms} polys={polys}")
                sys.stdout.flush()

    with open(out_tsv, "a") as f:
        f.write(f"# end={datetime.datetime.now(datetime.timezone.utc).isoformat()} "
                f"instances={n_inst} rows={n_rows} non_ok={n_err}\n")
    print(f"# done: {n_rows} rows, {n_err} non-OK; artifact {out_tsv}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

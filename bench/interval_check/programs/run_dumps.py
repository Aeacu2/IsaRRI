#!/usr/bin/env python3
"""Dump the isolating intervals of the seven competitor arms on SMT-Bench, the SMT held-out suite and
MPSolve-Bench (docs/LOGCF_PLAN_2026-10-08.md section 8). Counts, not timings: runs several cases at once.
Output: <suite>_<arm>.tsv (the dump tools' I/E/X lines) and <suite>_<arm>.log (one line per case: ok,
timeout, rc). A case already logged is skipped, so the run can be resumed.
Usage: run_dumps.py <suite,...> <arm,...> [--jobs N]"""
import concurrent.futures as cf, os, signal, subprocess, sys, threading
REPO = os.path.expanduser("~/Desktop/Dsc_LLVM"); H = f"{REPO}/Dsc/export/c_harness"; B = f"{H}/build"
HERE = os.path.dirname(os.path.abspath(__file__))
SRC = {"mpsolve": (f"{REPO}/benchmark_results/mpsolve_suite/coeffs", ".txt", False, 75),
       "smt": (f"{REPO}/benchmark_results/smt_bench/extracted", ".apolys", True, 60),
       "and": (f"{REPO}/benchmark_results/and_bench/coeffs", ".txt", False, 200),
       "ccluster": (f"{REPO}/benchmark_results/ccluster_suite/coeffs", ".txt", False, 80),
       "logcfbench": (f"{REPO}/benchmark_results/logcf_bench/coeffs", ".txt", False, 80),
       "heldout": (f"{REPO}/benchmark_results/smt_bench/heldout_2026-09-29/extracted", ".apolys", True, 60)}
def cmd(arm, multi, name, path):
    m = "stdin-multi" if multi else "stdin"
    if arm in ("msolve", "z3sqf", "libpolysqf"): return [f"{B}/lib_dump", arm, m, name], True
    if arm == "parisqf": return [f"{B}/pari_dump", m, name], True
    if arm == "cgal": return [f"{B}/cgal_dump", m, name], True
    if arm == "sagesqf": return ["sage", f"{H}/interval_dump/sage_dump.sage", "multi" if multi else "one", name, path], False
    if arm == "anewdsc": return [sys.executable, f"{H}/interval_dump/anewdsc_dump.py", "multi" if multi else "one", name, path], False
    raise SystemExit(arm)
def one(suite, arm, name):
    d, ext, multi, lim = SRC[suite]; path = f"{d}/{name}{ext}"
    c, stdin = cmd(arm, multi, name, path)
    if arm == "anewdsc" and multi: lim = 600
    fh = open(path) if stdin else subprocess.DEVNULL
    p = subprocess.Popen(c, stdin=fh, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
    try:
        out, err = p.communicate(timeout=lim); st = "ok" if p.returncode == 0 else f"rc={p.returncode}"
    except subprocess.TimeoutExpired:
        try: os.killpg(p.pid, signal.SIGKILL)
        except OSError: p.kill()          # killpg can be refused (seen 2026-10-09); kill the child itself
        out, err = p.communicate(); st = "timeout"
    if stdin: fh.close()
    return name, st, out if st == "ok" else "".join(l + "\n" for l in out.splitlines() if l.startswith("X"))
def main():
    suites, arms = sys.argv[1].split(","), sys.argv[2].split(",")
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 6
    for suite in suites:
        d, ext, _, _ = SRC[suite]
        names = sorted(f[:-len(ext)] for f in os.listdir(d) if f.endswith(ext))
        todo_f = f"{HERE}/todo_{suite}.tsv"   # AND-Bench, Ccluster: only (case, arm) pairs the arm completed in the
        only = {tuple(l.rstrip("\n").split("\t")) for l in open(todo_f)} if os.path.exists(todo_f) else None  # campaign, on inputs whose Sturm sequence is cached
        for arm in arms:
            if only is not None: names = sorted(c for c, a in only if a == arm)
            log = f"{HERE}/{suite}_{arm}.log"
            done = {l.split("\t")[0] for l in open(log)} if os.path.exists(log) else set()
            todo = [n for n in names if n not in done]
            lock = threading.Lock(); c = {}
            with open(f"{HERE}/{suite}_{arm}.tsv", "a") as fo, open(log, "a") as fl, cf.ThreadPoolExecutor(jobs) as ex:
                for name, st, out in ex.map(lambda n: one(suite, arm, n), todo):
                    fo.write(out); fl.write(f"{name}\t{st}\n"); fo.flush(); fl.flush(); c[st.split("=")[0]] = c.get(st.split("=")[0], 0) + 1
            print(suite, arm, len(names), "cases;", "this run:", c, flush=True)
if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""powsub-hash-compare.py -- T-e pre-pass for the thesis campaign.

Runs BOTH powsub_hash drivers (L4 artifact vs f3f96e19 control) over all 752
campaign cases (SMT 326 + MPSolve 131 + AND 295) and compares, per case, the
root count AND the FNV interval hash of the emitted windows.

THESIS_CAMPAIGN_PLAN.md §4 bar T-e: identical on every case; any mismatch stops
the campaign. This is a COUNT (no clock is read anywhere), so its output is
load-insensitive -- but it still burns CPU, so never run it beside a timing.

Per-case cap mirrors the campaign cap (150 s): a case capping on BOTH arms is
recorded BOTH_CAPPED (uncompared, not a mismatch -- the campaign PAR2 penalises
both arms equally there, so it cannot flip T-b). A case completing on exactly
one arm is a MISMATCH (stop).

Usage:
  python3 scripts/gates/powsub-hash-compare.py --out <out.tsv>
  (resume-safe: completed case rows in an existing --out are skipped)

Output TSV: suite, case, status, roots_l4, roots_ship, hash_l4, hash_ship, where
status in {MATCH, BOTH_CAPPED, MISMATCH, ERROR}.
"""
import argparse
import csv
import json
import os
import signal
import subprocess
import sys

REPO = "/Users/aeacu2/Desktop/Dsc_LLVM"
BUILD = f"{REPO}/Dsc/export/c_harness/build"
L4 = f"{BUILD}/powsub_hash_l4"
SHIP = f"{BUILD}/powsub_hash_ship"
CAP = 150  # per-case, per-arm -- mirrors the campaign cap

_live = set()


def _killpg(pid):
    try:
        os.killpg(pid, signal.SIGKILL)
    except Exception:
        pass


def run_one(binary, case, stdin_path):
    """Returns (roots, hash) or (None, 'TIMEOUT'/'ERROR...')."""
    with open(stdin_path) as fh:
        p = subprocess.Popen([binary, case], stdin=fh, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, text=True,
                             start_new_session=True)
    _live.add(p.pid)
    try:
        out, err = p.communicate(timeout=CAP + 15)
        to = False
    except subprocess.TimeoutExpired:
        _killpg(p.pid)
        try:
            p.communicate(timeout=10)
        except Exception:
            pass
        return None, "TIMEOUT"
    finally:
        _live.discard(p.pid)
    if p.returncode != 0:
        return None, f"ERROR:rc={p.returncode}:{(err or '').strip()[:100]}"
    hrows = [l for l in out.splitlines() if l.startswith("H\t")]
    if not hrows:
        return None, f"ERROR:no-H-rows:{(out.strip()[:80] + (err.strip()[:80]))!r}"
    h = __import__("hashlib").sha256("\n".join(hrows).encode()).hexdigest()[:16]
    r = sum(int(l.split("\t")[2]) for l in hrows)
    return r, h


def _on_signal(signum, frame):
    for pid in list(_live):
        _killpg(pid)
    sys.exit(128 + signum)


def load_cases():
    cases = []  # (suite, case, stdin_path)
    for row in json.load(open(f"{REPO}/benchmark_results/mpsolve_suite/cases_record.json")):
        cases.append(("mpsolve", row["name"],
                      f"{REPO}/benchmark_results/mpsolve_suite/coeffs/{row['name']}.txt"))
    for row in json.load(open(f"{REPO}/benchmark_results/and_bench/cases_record.json")):
        cases.append(("and", row["name"],
                      f"{REPO}/benchmark_results/and_bench/coeffs/{row['name']}.txt"))
    with open(f"{REPO}/benchmark_results/smt_bench/extracted/manifest.tsv") as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("instance"):
                continue
            inst = line.split("\t")[0]
            p = f"{REPO}/benchmark_results/smt_bench/extracted/{inst}.apolys"
            if os.path.exists(p):
                cases.append(("smt", inst, p))
    return cases


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    for b in (L4, SHIP):
        if not os.path.exists(b):
            sys.exit(f"FATAL: missing driver {b} -- run scripts/build-hashdrv.sh <l4|ship>")
    for signum in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(signum, _on_signal)
    try:
        os.setsid()
    except OSError:
        pass
    print(f"# hash-compare pid={os.getpid()} pgid={os.getpgid(0)}", file=sys.stderr)

    done = {}
    if os.path.exists(args.out):
        with open(args.out) as fh:
            for row in csv.DictReader(fh, delimiter="\t"):
                done[(row["suite"], row["case"])] = row
        print(f"# resuming: {len(done)} cases already recorded", file=sys.stderr)
    new = not os.path.exists(args.out) or os.path.getsize(args.out) == 0
    fh = open(args.out, "a", newline="")
    w = csv.writer(fh, delimiter="\t")
    if new:
        w.writerow(["suite", "case", "status", "roots_l4", "roots_ship",
                    "hash_l4", "hash_ship"])
        fh.flush()

    cases = load_cases()
    print(f"# {len(cases)} cases x 2 arms, cap {CAP}s", file=sys.stderr)
    n_match = n_cap = n_mm = n_err = 0
    for i, (suite, case, path) in enumerate(cases):
        if (suite, case) in done:
            r = done[(suite, case)]
            n_match += r["status"] == "MATCH"
            n_cap += r["status"] == "BOTH_CAPPED"
            n_mm += r["status"] == "MISMATCH"
            n_err += r["status"] == "ERROR"
            continue
        rl4, hl4 = run_one(L4, case, path)
        rsh, hsh = run_one(SHIP, case, path)
        if hl4 == "TIMEOUT" and hsh == "TIMEOUT":
            status = "BOTH_CAPPED"
            n_cap += 1
        elif rl4 is not None and rsh is not None and rl4 == rsh and hl4 == hsh:
            status = "MATCH"
            n_match += 1
        elif "ERROR" in str(hl4) or "ERROR" in str(hsh):
            status = "ERROR"
            n_err += 1
        else:
            # includes one-side TIMEOUT and any roots/hash divergence: stop-class
            status = "MISMATCH"
            n_mm += 1
        w.writerow([suite, case, status, rl4, rsh, hl4, hsh])
        fh.flush()
        if status != "MATCH":
            print(f"[{i+1}/{len(cases)}] {suite}/{case}: {status} "
                  f"roots={rl4}/{rsh} hash={hl4}/{hsh}", file=sys.stderr)
        elif (i + 1) % 50 == 0:
            print(f"[{i+1}/{len(cases)}] ... match={n_match} capped={n_cap} "
                  f"mismatch={n_mm} error={n_err}", file=sys.stderr)
    fh.close()
    print(f"DONE match={n_match} capped={n_cap} mismatch={n_mm} error={n_err}",
          file=sys.stderr)
    return 1 if (n_mm or n_err) else 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""All-roots comparison companion: RS-ANewDsc (Rouillier et al, Newton-accelerated Descartes
reference implementation -- https://who.rocq.inria.fr/Fabrice.Rouillier/AnewDesc/index.html).
Precompiled binary only (no source available); invoked as an external process per case with a
per-case wall-clock bound, same generators as the rest of this comparison ported line-for-line.

Default flags = "ANewDsc" (the tool's own recommended full config: subdivision at
pseudo-admissible points, bisection+Newton with full caching, partial Taylor shifts on
successful Newton steps, exact arithmetic above 2^30 working precision) plus -S 1 since our
test polynomials are known square-free (same assumption made implicitly by our own pipeline).

TIMING: self-timed via `-v 1`'s two getrusage snapshots on stderr ("Infos : Before/After
Isolation", "Since start : U(u),S(s),T(t),...") -- elapsed = After.t - Before.t. Since 2026-09-19
getrusage is interposed (build/anewdsc_wallclock.dylib) so t is WALL-CLOCK time, not CPU time; see
WALLCLOCK_DYLIB below. Excluding
process spawn/dynamic-load/input-parse (see benchmark_results/summaries/
mignotte_dyadic_center_rootcause_2026-07-09.md's "ANewDsc self-timing method": an external
wall-clock-minus-guessed-overhead approach was tried first and actually INVERTED a verdict at
small case sizes -- do not regress to that). `-v 1` (not higher) so debug printing doesn't
inflate the timed region; stdout still carries the plain isolating-interval list for the root
count, unaffected by the verbosity bump. min-of-9 (matches the doc's precedent for these
sub-millisecond-to-few-ms cases).

Run: python3 anewdsc_bench.py /path/to/test_descartes_osx
"""
import re
import subprocess
import sys
import tempfile
import time
import os

# Python 3.11+ refuses int<->str conversions above 4300 digits by default (CVE-2020-10735), and it
# raises rather than truncating. Our coefficients go far past that: case_92_kcluPure peaks at 24 664
# digits, case_82_geomOff at 10 138. In the FINAL-suite calibration this threw INSIDE THIS DRIVER,
# before test_descartes_osx was ever invoked, and the harness recorded the row as
# `ERROR:Traceback` -- indistinguishable from an anewdsc failure. 14 rows were affected and every
# one of them is OUR defect, not a limitation of anewdsc, which never got to run.
# The limit bites in BOTH directions: parsing here, and `f"{c}"` in write_poly_file on the way out.
# 0 disables it. See docs/FINAL_BENCHMARK_PLAN.md 4b.4 and memory
# competitor-failure-can-be-your-misconfig.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

REPS = 9
_INFO_RE = re.compile(
    r"Infos : (Before|After) Isolation\s*\n\s*Since start :\s*"
    r"[\d.]+\(u\),([\d.]+)\(s\),([\d.]+)\(t\)"
)

# WALL-CLOCK (2026-09-19, thesis campaign 2). The binary's own Before/After snapshots use getrusage,
# i.e. CPU time; every other arm is timed on a wall/steady clock. build/anewdsc_wallclock.dylib
# (anewdsc_wallclock.c) interposes getrusage so the SAME two snapshots read CLOCK_MONOTONIC_RAW and
# system time reads 0. Validated 2026-09-19: identical root counts on all 13 miscount inputs in both
# -i configs; a 2 s SIGSTOP inside isolation shows up in the figure (wall) and not without it (CPU).
# 🔴 Guarded, never silent: when the dylib is in use, a snapshot whose (s) column is not exactly 0
# means the interposer did not load (e.g. DYLD vars stripped), and the run is reported as
# WALLCLOCK_INACTIVE rather than quietly falling back to CPU time.
WALLCLOCK_DYLIB = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                               "build", "anewdsc_wallclock.dylib")
if not os.path.exists(WALLCLOCK_DYLIB):
    sys.exit(f"anewdsc_bench.py: missing {WALLCLOCK_DYLIB} -- build it (see anewdsc_wallclock.c)")
_ENV = dict(os.environ, DYLD_INSERT_LIBRARIES=WALLCLOCK_DYLIB)


def patterned_coeff(bits, seed, index):
    b = max(bits, 2)
    modulus = 2 ** (b + 1)
    half = 2 ** b
    j = index + 1
    s = seed + 17
    t = j + (seed % 97) + 3
    seed1 = seed + 1
    raw = (s * j**5 + 1103515245 * t**3 + 12345 * (j + 11) * seed1) % modulus
    v = raw - half
    if v == 0:
        v = 1 if index % 2 == 0 else -1
    return v


def dense_pattern(degree, bits, seed):
    coeffs = [patterned_coeff(bits, seed, i) for i in range(degree + 1)]
    if coeffs[-1] == 0:
        coeffs[-1] = 1
    return coeffs


def mignotte(n, tau):
    c = [0] * (n + 1)
    a = 2 ** tau
    c[0] = -2
    c[1] = 4 * a
    c[2] = -2 * a * a
    c[n] = 1
    return c


def mignotte_true(n, tau):
    """Non-dyadic-center Mignotte (a = 2^tau - 1): the canonical hard family; see
    benchmark_results/summaries/mignotte_dyadic_center_rootcause_2026-07-09.md."""
    c = [0] * (n + 1)
    a = 2 ** tau - 1
    c[0] = -2
    c[1] = 4 * a
    c[2] = -2 * a * a
    c[n] = 1
    return c


def write_poly_file(coeffs, path):
    with open(path, "w") as f:
        f.write(f"{len(coeffs) - 1}\n")
        for c in coeffs:
            f.write(f"{c}\n")


def self_timed_ms(stderr_text):
    """Parse the Before/After getrusage 't' totals from -v 1 stderr; return After.t - Before.t
    in milliseconds, or None if either snapshot is missing (caller falls back / flags it)."""
    totals = {}
    for m in _INFO_RE.finditer(stderr_text):
        which, sys_s, t = m.group(1), float(m.group(2)), float(m.group(3))
        if sys_s != 0.0:           # interposer not active: this would be CPU time -- refuse it
            raise RuntimeError("WALLCLOCK_INACTIVE")
        totals.setdefault(which, t)  # first match per label = the "Since start" line right after it
    if "Before" not in totals or "After" not in totals:
        return None
    return (totals["After"] - totals["Before"]) * 1000.0


def run_case(binary, name, coeffs, timeout_s=120, reps=REPS, extra=()):
    with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as tf:
        path = tf.name
    write_poly_file(coeffs, path)
    try:
        best_ms = None
        roots = None
        for _ in range(reps):
            try:
                result = subprocess.run(
                    [binary, "-S", "1", *extra, "-v", "1", path],
                    capture_output=True, text=True, timeout=timeout_s, env=_ENV,
                )
            except subprocess.TimeoutExpired:
                print(f"{name},deg={len(coeffs)-1},TIMED_OUT_AFTER={timeout_s}s")
                return
            ms = self_timed_ms(result.stderr)
            if ms is None:
                print(f"{name},deg={len(coeffs)-1},PARSE_FAILED,"
                      f"stderr_head={result.stderr[:200]!r}")
                return
            # stdout is the plain isolating-interval list, same shape at any -v level.
            line = result.stdout.strip()
            inner = line.strip("[]")
            roots = 0 if not inner else inner.count("],[") + 1
            best_ms = ms if best_ms is None else min(best_ms, ms)
        print(f"{name},deg={len(coeffs)-1},roots={roots},ms={best_ms:.4f}")
    finally:
        os.unlink(path)


def run_multi(binary, name, apolys_file, timeout_s=120, extra=()):
    """SMT-BENCH Phase 2 mode: read one dump-format poly per line ("A\t<deg>\t<c0>,..."),
    isolate EACH with a fresh `test_descartes_osx -S 1 -v 1` invocation (the precompiled
    binary takes one poly per process), sum self-timed ms and root counts. One process per
    poly is mandatory here -- the binary's interface is a single input file; the runner's
    subprocess cap is the sole supervisor for the whole (instance, arm, rep) unit."""
    total_ms = 0.0
    total_roots = 0
    npolys = 0
    for line in open(apolys_file):
        line = line.strip()
        if not line:
            continue
        parts = line.split("\t")
        if len(parts) < 3 or parts[0] != "A":
            continue
        coeffs = [c for c in parts[2].split(",") if c != ""]
        if not coeffs:
            continue
        with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as tf:
            path = tf.name
        write_poly_file(coeffs, path)
        try:
            try:
                result = subprocess.run(
                    [binary, "-S", "1", *extra, "-v", "1", path],
                    capture_output=True, text=True, timeout=timeout_s, env=_ENV,
                )
            except subprocess.TimeoutExpired:
                print(f"{name},TIMED_OUT_POLY={npolys},polys={npolys}")
                return
            ms = self_timed_ms(result.stderr)
            if ms is None:
                print(f"{name},PARSE_FAILED_POLY={npolys},stderr_head={result.stderr[:200]!r}")
                return
            line_out = result.stdout.strip()
            inner = line_out.strip("[]")
            roots = 0 if not inner else inner.count("],[") + 1
            print(f"P\t{npolys + 1}\t{len(coeffs) - 1}\t{roots}\t{ms}")
            total_ms += ms
            total_roots += roots
            npolys += 1
        finally:
            os.unlink(path)
    if npolys == 0:
        print(f"{name},NO_POLYS_PARSED")
        return
    print(f"{name},roots={total_roots},ms={total_ms:.4f},polys={npolys}")


def main():
    # --solve <binary> <name> <coeffs_file> [timeout_s] [reps]: run exactly ONE case, coeffs
    # (c0..cn, ascending degree, one comma-separated line) read from a file -- lets an
    # external driver feed any suite_v2_bench.cpp case (via its --dump-coeffs mode) without
    # hand-porting every generator into this file, same idea as the --solve-stdin/`stdin`
    # additions to the C++ harnesses and pari_solve_one.gp / sage_solve_one.sage.
    if len(sys.argv) > 1 and sys.argv[1] == "--solve":
        binary = sys.argv[2]
        name = sys.argv[3]
        # Kept as STRINGS, not ints. write_poly_file only formats them back to decimal and
        # run_case only takes len(), so parsing to int was a decimal->int->decimal round-trip that
        # bought nothing and was the sole reason huge-coefficient cases could fail here at all.
        with open(sys.argv[4]) as fh:
            coeffs = [c for c in fh.readline().strip().split(",") if c != ""]
        timeout_s = int(sys.argv[5]) if len(sys.argv) > 5 else 120
        reps = int(sys.argv[6]) if len(sys.argv) > 6 else REPS
        # [extra_flags] (2026-09-19, thesis campaign 2): one space-separated string of extra
        # test_descartes_osx flags, e.g. "-i 0" for the anewdsc_i0 sensitivity arm (the default
        # -i 1 is labelled [EXPERIMENTAL] in the tool's -h and causes most of its miscounts:
        # benchmark_results/summaries/miscount_attribution_2026-09-19.md).
        extra = sys.argv[7].split() if len(sys.argv) > 7 else ()
        run_case(binary, name, coeffs, timeout_s=timeout_s, reps=reps, extra=extra)
        return

    # --solve-multi <binary> <name> <apolys_file> [timeout_s]: SMT-BENCH Phase 2 mode --
    # one dump-format poly per line, sum isolation across the whole instance in-process.
    if len(sys.argv) > 1 and sys.argv[1] == "--solve-multi":
        binary = sys.argv[2]
        name = sys.argv[3]
        timeout_s = int(sys.argv[5]) if len(sys.argv) > 5 else 120
        extra = sys.argv[6].split() if len(sys.argv) > 6 else ()   # as --solve's [extra_flags]
        run_multi(binary, name, sys.argv[4], timeout_s=timeout_s, extra=extra)
        return

    binary = sys.argv[1] if len(sys.argv) > 1 else "test_descartes_osx"
    print(f"# RS-ANewDsc all-roots comparison (Newton-accelerated Descartes reference impl, "
          f"default ANewDsc config + -S 1, no fixed interval, self-timed via -v 1 getrusage "
          f"After-Before, min-of-{REPS}, {120}s/call cap)")

    run_case(binary, "dense_d128_b16", dense_pattern(128, 16, 1))
    run_case(binary, "dense_d256_b16", dense_pattern(256, 16, 1))
    run_case(binary, "dense_d512_b16", dense_pattern(512, 16, 1))
    run_case(binary, "dense_d1024_b16", dense_pattern(1024, 16, 1))
    run_case(binary, "dense_d512_b64", dense_pattern(512, 64, 2))

    run_case(binary, "mignotte_16_32", mignotte(16, 32))
    run_case(binary, "mignotte_32_64", mignotte(32, 64))
    run_case(binary, "mignotte_64_128", mignotte(64, 128))
    run_case(binary, "mignotte_32_128", mignotte(32, 128))
    run_case(binary, "mignotte_24_200", mignotte(24, 200))

    run_case(binary, "mignotte_true_16_32", mignotte_true(16, 32))
    run_case(binary, "mignotte_true_32_64", mignotte_true(32, 64))

    print("done")


if __name__ == "__main__":
    main()

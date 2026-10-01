# Generic single-case companion to sage_all_roots_bench.sage: usage
#   sage sage_solve_one.sage <name> <coeffs_file>
# where <coeffs_file> holds one line of comma-separated decimal coefficients (c0..cn,
# ascending degree). Lets an external driver feed any suite_v2_bench.cpp case (via its
# --dump-coeffs mode) without hand-porting every generator into this file -- same idea as
# the --solve-stdin addition to all_roots_vs_competitors_bench.cpp / cgal_descartes_bench.cpp's
# `stdin` mode / pari_solve_one.gp.
import sys
import time

name = sys.argv[1]
with open(sys.argv[2]) as fh:
    coeffs = [Integer(c) for c in fh.readline().strip().split(",") if c != ""]

R = PolynomialRing(ZZ, 'x')
f = R(coeffs)

# Warm-up: the FIRST real_root_intervals() in a fresh sage process pays the
# Bernstein-basis module import/compile cost (~100 ms, measured 2026-08-08: 102.8 ms
# vs 0.55 ms for the identical poly afterwards). Every cell here is a fresh process
# (final-suite-run.py spawns `sage` per rep), so without this EVERY cell's ms is
# inflated by ~100 ms. Pay it OUTSIDE the timed region (same convention as
# sage_all_roots_bench.sage).
R([-2, 0, 1]).real_root_intervals()

t0 = time.perf_counter()
roots = f.real_root_intervals()
t1 = time.perf_counter()
ms = (t1 - t0) * 1000.0
print(f"{name},deg={f.degree()},roots={len(roots)},ms={ms:.3f}")

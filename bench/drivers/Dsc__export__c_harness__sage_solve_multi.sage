# SMT-BENCH Phase 2 multi-poly companion to sage_solve_one.sage: usage
#   sage sage_solve_multi.sage <name> <apolys_file>
# where <apolys_file> holds one dump-format poly per line ("A\t<deg>\t<c0>,<c1>,...").
# Loops real_root_intervals over ALL of them IN-PROCESS (one sage session per instance,
# not per poly), sums isolation ms and root counts. The runner's subprocess cap is the
# sole supervisor -- same idea as pari_solve_multi.gp / suite_v2_bench.cpp --solve-stdin-multi.
import sys
import time

name = sys.argv[1]
total_ms = 0.0
total_roots = 0
npolys = 0

R = PolynomialRing(ZZ, 'x')

# Warm-up: the FIRST real_root_intervals() in a fresh sage process pays the
# Bernstein-basis module import/compile cost (~100 ms, measured 2026-08-08: 102.8 ms
# vs 0.55 ms for the identical poly afterwards). Every cell here is a fresh process,
# so without this the first poly's ms is inflated by ~100 ms. Pay it OUTSIDE the timed
# region (same convention as sage_all_roots_bench.sage).
R([-2, 0, 1]).real_root_intervals()

with open(sys.argv[2]) as fh:
    for line in fh:
        line = line.strip()
        if not line:
            continue
        parts = line.split("\t")
        if len(parts) < 3 or parts[0] != "A":
            continue
        coeffs = [Integer(c) for c in parts[2].split(",") if c != ""]
        if not coeffs:
            continue
        f = R(coeffs)
        t0 = time.perf_counter()
        roots = f.real_root_intervals()
        t1 = time.perf_counter()
        ms = (t1 - t0) * 1000.0
        print(f"P\t{npolys + 1}\t{f.degree()}\t{len(roots)}\t{ms:.6f}")
        total_ms += ms
        total_roots += len(roots)
        npolys += 1

if npolys == 0:
    sys.stderr.write("sage_solve_multi: no polynomials parsed\n")
    sys.exit(2)
print(f"{name},roots={total_roots},ms={total_ms:.6f},polys={npolys}")

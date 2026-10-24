# sage_dump.sage -- the isolating intervals of the Sage arm (real_roots(f, skip_squarefree=True), the call
# sage_solve_{one,multi}_sqf.sage time), for the interval check (docs/LOGCF_PLAN_2026-10-08.md section 8).
# NOT a timing tool. stdout: "I\t<name>\t<idx>\t<left>\t<right>" per root, "E\t<name>\t<idx>" per polynomial
# ("X\t<name>\t<idx>\t<exception>" if the call raises). Usage: sage sage_dump.sage one|multi <name> <file>
import sys
from sage.rings.polynomial.real_roots import real_roots
mode, name, path = sys.argv[1], sys.argv[2], sys.argv[3]
R = PolynomialRing(ZZ, 'x')
idx = 0
with open(path) as fh:
    for line in fh:
        line = line.strip()
        if not line:
            continue
        if mode == "multi":
            parts = line.split("\t")
            if len(parts) < 3 or parts[0] != "A":
                continue
            idx += 1
            cs = parts[2]
        else:
            idx = 1
            cs = line
        coeffs = [Integer(c) for c in cs.split(",") if c != ""]
        f = R(coeffs)
        if f.degree() < 1:
            continue
        try:
            roots = real_roots(f, skip_squarefree=True)
        except Exception as e:
            print(f"X\t{name}\t{idx}\t{type(e).__name__}")
            continue
        for (lo, hi), _ in roots:
            print(f"I\t{name}\t{idx}\t{QQ(lo)}\t{QQ(hi)}")
        print(f"E\t{name}\t{idx}")
        if mode != "multi":
            break

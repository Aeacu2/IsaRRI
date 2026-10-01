#!/usr/bin/env python3
"""certify-root-separation.py -- a CERTIFIED lower bound on the complex root separation of an
integer polynomial, and with it the flagship hypothesis's clauses, for inputs where Mahler's bound
is too weak (benchmark_results/summaries/hypothesis_check_2026-09-22.md, "undecided").

WHY. `isarri_correct`'s hypothesis bounds the depth measure mu, which is a function of the complex
root separation s (delta_P = root_sep / (4 R0), Dsc_Misc.thy). lifo-coverage-model.py decides it
rigorously only through Mahler's bound, whose factor n^-(n+2)/2 M(P)^-(n-1) is hopeless on wide
coefficients; PARI's numeric separation is evidence, not a proof. This script turns UNTRUSTED
approximations into a proof by exact integer arithmetic.

THE CERTIFICATE (Gerschgorin; self-contained). Let z_1..z_n be pairwise distinct and
W_i = P(z_i) / (lc * prod_{j != i} (z_i - z_j)) (Weierstrass corrections). Then
    det(x I - (diag(z) - 1 W^T)) = prod (x - z_j) + sum_i W_i prod_{j != i} (x - z_j) = P(x) / lc
(both sides are monic of degree n and agree at the n nodes). Gerschgorin's theorem on COLUMNS of
diag(z) - 1 W^T gives discs G_i = D(z_i - W_i, (n-1)|W_i|), contained in D_i = D(z_i, n|W_i|); if the
D_i are pairwise disjoint, so are the G_i, and each contains exactly one root. With
r = max n|W_i| <= D_min/4, where D_min = min |z_i - z_j|, any two roots are at least
D_min - 2r >= D_min/2 apart: s >= D_min / 2.

EXACT ARITHMETIC. z_i = w_i / 2^e with Gaussian integers w_i (the approximations rounded; how good
they are affects only whether the test passes, never its soundness). With
S_i = 2^(e n) P(z_i) = sum_j c_j w_i^j 2^(e(n-j)) and N_i = prod_{j != i} |w_i - w_j|^2, the test
n|W_i| <= D_min/4 is   16 n^2 |S_i|^2 <= m lc^2 N_i,   m = min |w_i - w_j|^2,  all integers. PARI/gp
evaluates it (GMP kernel) with bit-length bounds that only ever make it harder to pass:
|S|^2/(lc^2 N) < 2^t with t = exponent(num) - exponent(den) + 1, and pass iff t_max <= exponent(m).
Then log2 s >= exponent(m)/2 - e - 1.

The approximations come from MPSolve 3.2.1 (third_party/root_isolators), which is NOT trusted.

Usage:
  certify-root-separation.py CASE [CASE ...] [--suite and] [--which P|Q|both] [--e 128] [--out FILE.tsv]
Writes one row per polynomial: suite case which len n e log2_sep_certified clauses verdict secs.
"""
import argparse, fractions, importlib.util, math, os, subprocess, sys, tempfile, time
from decimal import Decimal

sys.set_int_max_str_digits(0)
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MPSOLVE = os.path.join(ROOT, "third_party/root_isolators/mpsolve-3.2.1/src/mpsolve/mpsolve")
_spec = importlib.util.spec_from_file_location("cdh", os.path.join(ROOT, "scripts/check-depth-hypothesis.py"))
cdh = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(cdh)
_spec2 = importlib.util.spec_from_file_location("lcm", os.path.join(ROOT, "scripts/lifo-coverage-model.py"))
lcm = importlib.util.module_from_spec(_spec2); _spec2.loader.exec_module(lcm)

GP_PROG = r"""
default(parisizemax, 4000000000);
default(threadsizemax, 1000000000);
default(nbthreads, 4);
f(k)=my(w=wr[k]+I*wi[k],acc=c[n+1],v=vector(n-1),t=0,num,den);\
 for(s=1,n,acc=acc*w+shift(c[n-s+1],e*s));\
 num=16*n^2*norm(acc);\
 for(j=1,n,if(j!=k,t++;v[t]=(wr[k]-wr[j])^2+(wi[k]-wi[j])^2));\
 if(vecmin(v)==0,return([10^9,0]));\
 den=vecprod(v)*c[n+1]^2;\
 [if(num==0,-10^9,exponent(num)-exponent(den)+1), vecmin(v)];
export(n,e,c,wr,wi,f);
R=parvector(n,k,f(k));
tmax=vecmax(vector(n,k,R[k][1])); m=vecmin(vector(n,k,R[k][2]));
print("RESULT ",tmax," ",if(m>0,exponent(m),-1));
quit;
"""


def mpsolve_roots(coeffs, workdir, digits=40):
    pol = os.path.join(workdir, "p.pol")
    with open(pol, "w") as f:
        f.write("Monomial;\nReal;\nInteger;\nDegree=%d;\n" % (len(coeffs) - 1))
        f.write("\n".join(str(c) for c in coeffs) + "\n")
    goal = ["-Gi"] if digits is None else ["-Ga", f"-o{digits}"]   # isolate mode is much faster
    out = subprocess.run([MPSOLVE, *goal, "-Ob", "-j4", pol], capture_output=True, text=True, check=True).stdout
    roots = []
    for ln in out.split("\n"):
        p = ln.split()
        if len(p) == 2:
            roots.append((fractions.Fraction(Decimal(p[0])), fractions.Fraction(Decimal(p[1]))))
    return roots


def certify(coeffs, e, max_e=1024):
    """Retry at doubled precision until the test passes or e exceeds max_e.
    -> (log2 lower bound on the complex root separation or None, detail)."""
    ls, why = certify_at(coeffs, 64, digits=None)           # first: MPSolve's isolation output
    if ls is not None:
        return ls, "e=64 isolate " + why
    while e <= max_e:
        ls, why = certify_at(coeffs, e, digits=int(e / 3.3) + 10)
        if ls is not None:
            return ls, f"e={e} " + why
        e *= 2
    return None, why


def certify_at(coeffs, e, digits):
    n = len(coeffs) - 1
    with tempfile.TemporaryDirectory() as td:
        roots = mpsolve_roots(coeffs, td, digits)
        if len(roots) != n:
            return None, f"mpsolve returned {len(roots)} of {n}"
        wr = [round(x * 2 ** e) for x, _ in roots]
        wi = [round(y * 2 ** e) for _, y in roots]
        g = os.path.join(td, "cert.gp")
        with open(g, "w") as f:
            f.write(f"n={n};\ne={e};\n")
            f.write("c=[" + ",".join(str(x) for x in coeffs) + "];\n")
            f.write("wr=[" + ",".join(str(x) for x in wr) + "];\n")
            f.write("wi=[" + ",".join(str(x) for x in wi) + "];\n")
            f.write(GP_PROG)
        out = subprocess.run(["gp", "-q", "-s", "1000000000", g], capture_output=True, text=True).stdout
    res = [ln for ln in out.split("\n") if ln.startswith("RESULT ")]
    if not res:
        return None, "gp produced no result: " + out[-300:]
    tmax, em = (int(x) for x in res[0].split()[1:])
    if em < 0:
        return None, "approximations not distinct"
    if tmax > em:
        return None, f"discs not disjoint (t_max={tmax} > exponent(m)={em})"
    return em / 2 - e - 1, f"t_max={tmax} exponent(m)={em}"


def selftest():
    """The test must be able to FAIL: planted bad approximations are rejected, good ones pass."""
    global mpsolve_roots
    real = mpsolve_roots
    ys = [-6, 11, -6, 1]                                     # (x-1)(x-2)(x-3): sep = 1
    ok, _ = certify_at(ys, 64, 30)
    assert ok is not None and -1.01 <= ok <= 0, ok           # a lower bound, and not a loose one
    F = fractions.Fraction
    for bad in ([(F(1), 0), (F(2), 0), (F(7, 2), 0)],        # one approximation off by 1/2
                [(F(1), 0), (F(2), 0), (F(2), 0)],           # two coincide
                [(F(1), 0), (F(2), 0), (F(3), 0), (F(4), 0)]):  # wrong count
        mpsolve_roots = lambda c, td, d=40, bad=bad: bad
        try:
            got, why = certify_at(ys, 64, 30)
        finally:
            mpsolve_roots = real
        assert got is None, (bad, got, why)
    print("selftest: 1 pass, 3 planted failures rejected")


def main():
    if sys.argv[1:] == ["--selftest"]:
        return selftest()
    ap = argparse.ArgumentParser()
    ap.add_argument("cases", nargs="+")
    ap.add_argument("--suite", default="and")
    ap.add_argument("--which", default="both", choices=["P", "Q", "both"])
    ap.add_argument("--e", type=int, default=128)
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    d = {"and": "benchmark_results/and_bench/coeffs", "mpsolve": "benchmark_results/mpsolve_suite/coeffs"}[a.suite]
    rows = []
    for case in a.cases:
        body = open(os.path.join(ROOT, d, case + ".txt")).read().strip().rstrip(",")
        ys = [int(c) for c in body.split(",")]
        dd, q = cdh.reduce_poly(ys)
        for which, zs in (("P", ys), ("Q", q)):
            if zs is None or (a.which != "both" and a.which != which):
                continue
            t0 = time.time()
            ls, why = certify(zs, a.e)
            verdict = "UNDECIDED" if ls is None else ("PASS_CERT" if lcm.lifo_ok(zs, ls) else "FAIL_CERT")
            row = [a.suite, case, which, len(zs), len(zs) - 1, a.e,
                   "" if ls is None else f"{ls:.1f}", why, verdict, f"{time.time() - t0:.0f}"]
            print("\t".join(map(str, row)), flush=True)
            rows.append(row)
    if a.out:
        with open(a.out, "w") as f:
            f.write("suite\tcase\twhich\tlen\tn\te\tlog2_sep_certified\tdetail\tverdict\tsecs\n")
            for r in rows:
                f.write("\t".join(map(str, r)) + "\n")


if __name__ == "__main__":
    main()

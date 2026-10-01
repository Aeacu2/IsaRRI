#!/usr/bin/env python3
"""Exact count of the real roots of a squarefree integer polynomial by a Gerschgorin certificate,
for inputs too large for a Sturm sequence (B2, 2026-09-26). Neither Descartes' rule nor PARI's
root counting is used; PARI/gp only does exact integer arithmetic.

  gerschgorin_real_count.py <coefficient file | comma-separated coefficients> [--e 128]

THE ARGUMENT. Let z_1..z_n be pairwise distinct (untrusted MPSolve approximations, rounded to
Gaussian integers w_k at scale 2^e) and W_k the Weierstrass corrections. Then P/lc is the
characteristic polynomial of diag(z) - 1 W^T, whose column Gerschgorin discs G_k lie in
D_k = D(z_k, n|W_k|) (scripts/certify-root-separation.py). If the D_k are pairwise disjoint, each
G_k, hence each D_k, contains exactly one root r_k, and these are all the roots.
  * If D_k misses the real axis, r_k is not real.
  * Let D'_k be the disc centred at Re z_k with radius R_k + |Im z_k| (R_k an upper bound on the
    radius of D_k). D'_k contains D_k, so r_k, and is symmetric about the real axis, so conj(r_k).
    If D'_k is disjoint from every D_j (j != k), then conj(r_k) is no r_j with j != k, so
    conj(r_k) = r_k: r_k is real.
If every disc is classified, the number of real roots is the number of discs classified real.
EXACT ARITHMETIC, in the scaled coordinates w = 2^e z: 16 rho_k^2 < 2^t_k where rho_k is the scaled
radius n|W_k| 2^e (as in certify-root-separation.py), so R_k = 2^(ceil(t_k/2) - 2) >= rho_k. All
comparisons are between integers: |w_i - w_j|^2 > (R_i + R_j)^2 for disjointness; |Im w_k| > R_k
for "not real"; (Re w_k - Re w_j)^2 + (Im w_j)^2 > (R_k + |Im w_k| + R_j)^2 for all j != k for "real".
Poor approximations can only make the certificate fail, never give a wrong count.
"""
import importlib.util, os, subprocess, sys, tempfile

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.set_int_max_str_digits(0)
_spec = importlib.util.spec_from_file_location("crs", os.path.join(REPO, "scripts/certify-root-separation.py"))
crs = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(crs)

GP = r"""
default(parisizemax, 8000000000);
t(k)=my(w=wr[k]+I*wi[k],acc=c[n+1],v=vector(n-1),q=0,num,den);\
 for(s=1,n,acc=acc*w+shift(c[n-s+1],e*s));\
 num=16*n^2*norm(acc);\
 for(j=1,n,if(j!=k,q++;v[q]=(wr[k]-wr[j])^2+(wi[k]-wi[j])^2));\
 if(vecmin(v)==0,error("coincident approximations"));\
 den=vecprod(v)*c[n+1]^2;\
 if(num==0,-10^6,exponent(num)-exponent(den)+1);
T=vector(n,k,t(k)); R=vector(n,k,2^max(0,ceil(T[k]/2)-2));
ok=1; for(i=1,n,for(j=i+1,n,if((wr[i]-wr[j])^2+(wi[i]-wi[j])^2<=(R[i]+R[j])^2,ok=0;break(2))));
if(!ok, print("RESULT overlap"); quit);
{cr=0; cn=0; cu=0;
for(k=1,n, if(abs(wi[k])>R[k], cn++,
  my(rr=R[k]+abs(wi[k]), good=1);
  for(j=1,n,if(j!=k && (wr[k]-wr[j])^2+wi[j]^2<=(rr+R[j])^2, good=0; break));
  if(good, cr++, cu++)))};
print("RESULT ", cr, " ", cn, " ", cu);
quit;
"""


def count(coeffs, e):
    n = len(coeffs) - 1
    with tempfile.TemporaryDirectory() as td:
        roots = crs.mpsolve_roots(coeffs, td, int(e / 3.3) + 10)
        if len(roots) != n:
            return None, f"mpsolve returned {len(roots)} of {n}"
        wr = [round(x * 2 ** e) for x, _ in roots]
        wi = [round(y * 2 ** e) for _, y in roots]
        g = os.path.join(td, "g.gp")
        with open(g, "w") as f:
            f.write(f"n={n};\ne={e};\nc=[{','.join(map(str, coeffs))}];\nwr=[{','.join(map(str, wr))}];\nwi=[{','.join(map(str, wi))}];\n")
            f.write(GP)
        out = subprocess.run(["gp", "-q", g], capture_output=True, text=True).stdout
    res = [l for l in out.splitlines() if l.startswith("RESULT")]
    if not res or res[0] == "RESULT overlap":
        return None, (res[0] if res else "gp: " + out[-200:])
    try:
        real, nonreal, unres = map(int, res[0].split()[1:])
    except ValueError:
        return None, "gp error (e.g. coincident approximations at this precision)"
    if unres or real + nonreal != n:
        return None, f"{unres} discs unclassified"
    return real, f"e={e}: {real} real, {nonreal} non-real discs"


def selftest():
    """Good approximations certify the right count; planted bad ones must fail, never miscount."""
    import fractions
    F = fractions.Fraction
    ys = [-6, 11, -12, 12, -6, 1]                     # (x-1)(x-2)(x-3)(x^2+1): 3 real
    r, _ = count(ys, 128)
    assert r == 3, r
    real = crs.mpsolve_roots
    good = real(ys, tempfile.mkdtemp(), 60)
    for bad in ([(F(1), 0), (F(2), 0), (F(7, 2), 0), (F(0), F(1)), (F(0), F(-1))],   # one root off
                [(F(1), 0), (F(2), 0), (F(3), 0), (F(0), F(1)), (F(1, 10**30), F(-1))]):  # conjugate pair broken
        crs.mpsolve_roots = lambda c, td, d=40, bad=bad: bad
        try:
            got, why = count(ys, 128)
        finally:
            crs.mpsolve_roots = real
        assert got is None or got == 3, (bad, got, why)
    print("selftest: correct count certified; planted bad approximations never give a wrong count")


def main():
    if "--selftest" in sys.argv:
        selftest(); return 0
    arg = sys.argv[1]
    cs = open(arg).read().strip() if os.path.exists(arg) else arg
    coeffs = [int(x) for x in cs.split(",")]
    e = int(sys.argv[sys.argv.index("--e") + 1]) if "--e" in sys.argv else 128
    while e <= 4096:
        r, why = count(coeffs, e)
        print(r, why, flush=True)
        if r is not None:
            return 0
        e *= 2
    return 1


if __name__ == "__main__":
    sys.exit(main())

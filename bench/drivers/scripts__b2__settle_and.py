#!/usr/bin/env python3
"""Settle every AND-Bench case on which the arms' counts disagree (or on which an arm's count
differed from the campaign's recorded reference), WITHOUT PARI's polsturm (a Descartes/Uspensky
count): by a genuine Sturm sequence (scripts/b2/sturm_windows.gp, sturmtotal) and, where a closed
form applies, by the classical theorem that the orthogonal polynomials of degree n have n distinct
real roots, after verifying exactly that the input is a nonzero scalar multiple of that polynomial.

  python3 scripts/b2/settle_and.py [--budget S] [--cases a,b]

Gauss families: P = f^2 - 1 = (f-1)(f+1). f is recovered exactly (issquare(P+1)); f-1 and f+1 are
coprime (a common root r would give f(r) = 1 = -1), so the count is the sum of their Sturm totals.
Writes benchmark_results/b2_windows/and_disputes.tsv. A count, not a timing.
"""
import csv, hashlib, os, subprocess, sys, tempfile

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
B2 = os.path.join(REPO, "scripts/b2")
CSV = os.path.join(REPO, "benchmark_results/data/thesis_campaign2_2026-09-18/and_results.csv")
COEFFS = os.path.join(REPO, "benchmark_results/and_bench/coeffs")
OUT = os.path.join(REPO, "benchmark_results/b2_windows/and_disputes.tsv")

GP_FN = r'''
analytic(P, fam, n) = {
  my(R = if (fam == "chebyshev_T", polchebyshev(n, 1), fam == "chebyshev_U", polchebyshev(n, 2),
             fam == "hermite", polhermite(n), fam == "legendre", pollegendre(n), 0));
  if (R == 0, return(-1));
  if (poldegree(P) != n || P * pollead(R) != R * pollead(P), return(-2));
  n;
}
settle(P, fam) = {
  my(f);
  if (fam == "gauss_sqrtn" || fam == "gauss_logn",
    if (!issquare(P + 1, &f), return([-3, "P+1 not a square"]));
    return([sturmtotal(f - 1) + sturmtotal(f + 1), "Sturm on f-1 and f+1"]));
  [sturmtotal(P), "Sturm"];
}
'''


def disputed():
    rows = list(csv.DictReader(open(CSV)))
    by = {}
    for r in rows:
        by.setdefault(r["case"], []).append(r)
    out = []
    for case, rs in by.items():
        counts = {r["solver"]: int(r["roots"]) for r in rs if r["status"] == "OK"}
        o = int(rs[0]["oracle"])
        if len(set(counts.values())) > 1 or (o >= 0 and any(v != o for v in counts.values())):
            out.append((case, rs[0]["family"], int(rs[0]["degree"]), o, counts))
    return sorted(out)


def main():
    budget = int(sys.argv[sys.argv.index("--budget") + 1]) if "--budget" in sys.argv else 14400
    only = set(sys.argv[sys.argv.index("--cases") + 1].split(",")) if "--cases" in sys.argv else None
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    done = set()
    if os.path.exists(OUT):
        done = {l.split("\t")[0] for l in open(OUT) if not l.startswith("case\t")}
    fo = open(OUT, "a")
    if not done:
        fo.write("case\tfamily\tdegree\tinput_sha256\tchecker\trecorded_reference\tanalytic\tsturm\tmethod\tseconds\tarm_counts\n")
    commit = subprocess.run(["git", "-C", REPO, "rev-parse", "--short", "HEAD"], capture_output=True, text=True).stdout.strip()
    for case, fam, deg, o, counts in disputed():
        if case in done or (only and case not in only):
            continue
        raw = open(os.path.join(COEFFS, case + ".txt"), "rb").read()
        sha = hashlib.sha256(raw).hexdigest(); cs = raw.decode().strip()
        prog = [f'default(parisizemax, 2^33);', f'read("{B2}/sturm_windows.gp");', GP_FN,
                f'P = Polrev([{cs}]);',
                f'print("A\\t", analytic(P, "{fam}", {deg}));',
                f't0 = getabstime(); iferr(my(s = alarm({budget}, settle(P, "{fam}"))); print("S\\t", s[1], "\\t", s[2]), E, print("S\\t-\\t", Str(errname(E)))); print("T\\t", (getabstime() - t0) / 1000.);']
        # The program goes to gp through a file rather than stdin (d2896's run died without output, 2026-09-27).
        with tempfile.TemporaryDirectory() as td:
            pf = os.path.join(td, "settle.gp")
            open(pf, "w").write("\n".join(prog) + "\n")
            r = subprocess.run(["gp", "-q", "-D", "readline=0", pf], stdin=subprocess.DEVNULL, capture_output=True, text=True)
        val = {}
        for line in r.stdout.splitlines():
            f = line.split("\t")
            val[f[0]] = f[1:]
        a = val.get("A", ["gp-died"])[0].strip()
        s, method = (val.get("S", ["-", "gp-died"]) + ["-"])[:2]
        secs = val.get("T", ["-"])[0].strip()
        arms = ",".join(f"{k}={v}" for k, v in sorted(counts.items()))
        fo.write(f"{case}\t{fam}\t{deg}\t{sha}\t{commit}\t{o}\t{a}\t{s.strip()}\t{method.strip()}\t{secs}\t{arms}\n")
        fo.flush()
        print(case, "analytic", a, "sturm", s.strip(), method.strip(), secs, flush=True)


if __name__ == "__main__":
    main()

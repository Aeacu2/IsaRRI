#!/usr/bin/env python3
"""Gauss rungs P = f^2 - 1: recover f exactly (P + 1 must be a perfect square), then count the real
roots of f - 1 and f + 1 with the Gerschgorin certificate (gerschgorin_real_count.py). f - 1 and
f + 1 are coprime, so the count of P is the sum. Writes benchmark_results/b2_windows/and_gauss_gerschgorin.tsv."""
import os, subprocess, sys, tempfile, time
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OUT = os.path.join(REPO, "benchmark_results/b2_windows/and_gauss_gerschgorin.tsv")
sys.set_int_max_str_digits(0)
for case in sys.argv[1:]:
    cs = open(os.path.join(REPO, "benchmark_results/and_bench/coeffs", case + ".txt")).read().strip()
    # default(parisizemax) must stand alone on its line: gp discards the rest of the line on which the
    # stack limit changes, so everything after it silently never ran and f was never printed (2026-09-27).
    with tempfile.TemporaryDirectory() as td:
        pf = os.path.join(td, "p.gp")
        open(pf, "w").write(f"P=Polrev([{cs}]);\n")
        gp = f'default(parisizemax,2^33)\nread("{pf}"); if(!issquare(P+1,&f), print("NOSQUARE"), print(Vecrev(f)));'
        r = subprocess.run(["gp", "-q", "-D", "readline=0"], input=gp + "\n", capture_output=True, text=True)
    out = next((l for l in r.stdout.splitlines() if l.startswith("[") or l.startswith("NOSQUARE")), "")
    if out.startswith("NOSQUARE"):
        open(OUT, "a").write(f"{case}\t-\t-\t-\tP+1 not a square\n"); continue
    if not out.startswith("["):
        open(OUT, "a").write(f"{case}\t-\t-\t-\tgp failed recovering f (rc {r.returncode}): {r.stderr.strip()[-120:]!r}\n"); continue
    f = [int(x) for x in out.strip("[]").replace(" ", "").split(",")]
    res = []
    for sgn in (-1, 1):
        g = list(f); g[0] += sgn
        t0 = time.time()
        r = subprocess.run([sys.executable, os.path.join(REPO, "scripts/b2/gerschgorin_real_count.py"), ",".join(map(str, g))],
                           capture_output=True, text=True).stdout.strip().splitlines()
        last = r[-1] if r else "None no output"
        res.append((last.split()[0], last, round(time.time() - t0, 1)))
    tot = "-" if any(x[0] == "None" for x in res) else str(int(res[0][0]) + int(res[1][0]))
    open(OUT, "a").write(f"{case}\t{res[0][0]}\t{res[1][0]}\t{tot}\t{res[0][1]} ({res[0][2]} s); {res[1][1]} ({res[1][2]} s)\n")
    print(case, tot, flush=True)

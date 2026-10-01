#!/usr/bin/env python3
"""Check every window IsaRRI returns for one input, with a genuine Sturm sequence.

  python3 bench/sturm/check_one.py <input file> [--gmp PREFIX] [--budget SECONDS]

The input is one line of comma-separated integer coefficients in ascending degree, or an SMT-Bench
.apolys file (lines "A<TAB>deg<TAB>coefficients"). The script builds window_dump.c against the
public export (export/isarri.ll), runs it (out_cap = number of coefficients, nfloor 22, hcap 32,
dlt 8), and checks each polynomial's windows with sturm_windows.gp: point windows are roots; each
open window holds exactly one root; no root lies in two windows; the window counts per half equal
the Sturm counts and the reported counts; the zero flag; the dyadic and reflected decoding.
Prints one line per polynomial: index, OK/FAIL/UNCHECKED, positive and negative Sturm counts, the
zero flag, and the reasons for a failure. Needs clang, GMP and PARI/GP (used only for exact
integer arithmetic; its own root counting is not used).
"""
import os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


def main():
    path = sys.argv[1]
    gmp = sys.argv[sys.argv.index("--gmp") + 1] if "--gmp" in sys.argv else \
        (subprocess.run(["brew", "--prefix", "gmp"], capture_output=True, text=True).stdout.strip() or "/opt/homebrew")
    budget = int(sys.argv[sys.argv.index("--budget") + 1]) if "--budget" in sys.argv else 600
    exe = os.path.join(tempfile.gettempdir(), "isarri_window_dump")
    subprocess.run(["clang", "-O2", "-w", f"-I{ROOT}/export", f"-I{gmp}/include", f"{HERE}/window_dump.c",
                    f"{ROOT}/export/isarri.ll", f"{ROOT}/runtime/lib_isabelle_llvm.c", f"-L{gmp}/lib", "-lgmp", "-o", exe], check=True)
    out = subprocess.run([exe, path], capture_output=True, text=True, check=True).stdout
    coeffs = []
    for line in open(path):
        if line.startswith("A\t"):
            coeffs.append(line.rstrip("\n").split("\t")[2])
        elif line[:1].isdigit() or line[:1] == "-":
            coeffs.append(line.strip())
    gp = [f'read("{HERE}/sturm_windows.gp");']
    cur = None
    def flush(p):
        W = "[" + ",".join(f"[{s},{l},{r},{k}]" for s, l, r, k in p["w"]) + "]"
        gp.append(f'iferr(alarm({budget}, check({p["i"]}, Polrev([{coeffs[p["i"] - 1]}]), {p["pos"]}, {p["neg"]}, {p["xs0"]}, {W})), '
                  f'E, print({p["i"]}, "\\tUNCHECKED\\t", Str(errname(E))));')
    for line in out.splitlines():
        f = line.split()
        if f[0] == "P":
            if cur:
                flush(cur)
            cur = {"i": int(f[1]), "pos": f[2], "neg": f[3], "xs0": f[4], "w": []}
        elif f[0] in "+-":
            cur["w"].append((1 if f[0] == "+" else -1, f[1], f[2], f[3]))
    if cur:
        flush(cur)
    r = subprocess.run(["gp", "-q", "-D", "readline=0"], input="\n".join(gp) + "\n", capture_output=True, text=True)
    sys.stdout.write(r.stdout)
    return 0 if "FAIL" not in r.stdout else 1


if __name__ == "__main__":
    sys.exit(main())

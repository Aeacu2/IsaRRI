#!/usr/bin/env python3
"""anewdsc_dump.py -- the isolating intervals ANewDsc prints (test_descartes_osx -S 1, the default
configuration the campaign's `anewdsc` arm runs), for the interval check
(docs/LOGCF_PLAN_2026-10-08.md section 8). NOT a timing tool. One process per polynomial, as the tool
requires. stdout: "I\t<name>\t<idx>\t<left>\t<right>" per root, "E\t<name>\t<idx>" per polynomial,
"X\t<name>\t<idx>\t<reason>" when the tool gives no list within the per-polynomial limit.
Usage: anewdsc_dump.py one|multi <name> <file> [limit_s]"""
import os, re, subprocess, sys, tempfile
from fractions import Fraction
sys.set_int_max_str_digits(0)
BIN = os.path.expanduser("~/Downloads/test_descartes_osx")
mode, name, path = sys.argv[1:4]
limit = float(sys.argv[4]) if len(sys.argv) > 4 else 72.0
END = re.compile(r"(-?\d+)/2\^(-?\d+)")
def val(m):
    n, k = int(m.group(1)), int(m.group(2))
    return Fraction(n, 2 ** k) if k >= 0 else Fraction(n * 2 ** (-k))
idx = 0
tf = tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False); tf.close()
try:
    for line in open(path):
        line = line.strip()
        if not line:
            continue
        if mode == "multi":
            p = line.split("\t")
            if len(p) < 3 or p[0] != "A":
                continue
            idx += 1; cs = p[2]
        else:
            idx = 1; cs = line
        coeffs = [c for c in cs.split(",") if c != ""]
        while len(coeffs) > 1 and int(coeffs[-1]) == 0:
            coeffs.pop()
        if len(coeffs) < 2:
            continue
        with open(tf.name, "w") as f:
            f.write(f"{len(coeffs) - 1}\n" + "\n".join(coeffs) + "\n")
        try:
            r = subprocess.run([BIN, "-S", "1", tf.name], capture_output=True, text=True, timeout=limit)
        except subprocess.TimeoutExpired:
            print(f"X\t{name}\t{idx}\ttimeout"); continue
        out = r.stdout.strip()
        if r.returncode != 0 or not out.startswith("["):
            print(f"X\t{name}\t{idx}\trc={r.returncode}"); continue
        ends = [val(m) for m in END.finditer(out)]
        if len(ends) % 2 or END.sub("", out).strip("[], \n"):
            print(f"X\t{name}\t{idx}\tunparsed"); continue
        for i in range(0, len(ends), 2):
            print(f"I\t{name}\t{idx}\t{ends[i]}\t{ends[i + 1]}")
        print(f"E\t{name}\t{idx}")
        if mode != "multi":
            break
finally:
    os.unlink(tf.name)

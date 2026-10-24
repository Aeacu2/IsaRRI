#!/usr/bin/env python3
"""<suite>_<arm>.tsv (I/E/X lines of the dump tools) -> windows_<suite>_<arm>.tsv in the format of
scripts/b2/check_risolate_windows.py (name, idx, 1, centre, radius; a reversed interval keeps its negative
radius and fails the check). PARI's lines carry h and v and are written as name, idx, h, v, left, right for
check_reduced_windows.py. Usage: to_windows.py <suite> <arm>"""
import sys
from fractions import Fraction as F
sys.set_int_max_str_digits(0)
suite, arm = sys.argv[1:3]
n = p = x = 0; seen = set()
with open(f"windows_{suite}_{arm}.tsv", "w") as o:
    for line in open(f"{suite}_{arm}.tsv"):
        f = line.rstrip("\n").split("\t")
        if f[0] == "X": x += 1; continue
        if f[0] == "E": p += 1; continue
        if f[0] != "I": continue
        if arm == "parisqf":
            assert len(f) == 7, f[:3]
            o.write("\t".join(f[1:]) + "\n")
        else:
            assert len(f) == 5, f[:3]
            l, r = F(f[3]), F(f[4]); o.write(f"{f[1]}\t{f[2]}\t1\t{(l + r) / 2}\t{(r - l) / 2}\n")
        n += 1
print(f"{suite} {arm}: {n} intervals, {p} polynomials dumped, {x} not dumped (X)")

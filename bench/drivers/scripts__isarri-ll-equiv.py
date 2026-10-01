#!/usr/bin/env python3
"""Body-level equivalence of the renamed IsaRRI .ll against the shipped one (supplement plan phase 4).

Usage: scripts/isarri-ll-equiv.py <shipped.ll> <isarri.ll> <NAMES.tsv>

The shipped file exports seven entries; IsaRRI exports one. So the comparison is over the functions
reachable from the flagship's three public symbols in the shipped file. Every symbol in that set is
renamed by the approved map (an LLVM function is named <Theory>_<constant>, so a map key is replaced
where it stands between `_`/start and `_`/end of the symbol), and then:
  1. the renamed reachable set must equal the set of functions defined in isarri.ll;
  2. every body must be byte-identical after renaming the symbols it references;
  3. every `declare` the reachable set needs must be present, and no extra `define` may exist.
Exit 0 only if all hold. Prints each difference.
"""
import re, sys

if len(sys.argv) != 4:
    sys.exit(__doc__)
old_path, new_path, names_path = sys.argv[1:]

names = {}
for line in open(names_path):
    if line.startswith("#") or not line.strip():
        continue
    old, new, kind = line.rstrip("\n").split("\t")
    if kind == "name":
        names[old] = new
PUBLIC = {"all_dsc_powsub_main": "isarri", "dsc_mpzb_sgn": "isarri_mpz_sgn", "mpzb_free": "isarri_mpz_free"}
keys = sorted(names, key=len, reverse=True)

def parse(path):
    txt = open(path, encoding="utf-8").read()
    defs, decls, other = {}, {}, []
    cur, buf = None, []
    for line in txt.split("\n"):
        if cur is None:
            m = re.match(r"^define\s.*?@([\w.$]+)\s*\(", line)
            if m:
                cur, buf = m.group(1), [line]
                continue
            m = re.match(r"^declare\s.*?@([\w.$]+)\s*\(", line)
            if m:
                decls[m.group(1)] = line
            elif line.strip() and not line.startswith(";"):
                other.append(line)
        else:
            buf.append(line)
            if line == "}":
                defs[cur] = "\n".join(buf)
                cur = None
    return defs, decls, other

SYM = re.compile(r"@([\w.$]+)")
def callees(body):
    return set(SYM.findall(body))

def rename_sym(s):
    if s in PUBLIC:
        return PUBLIC[s]
    out = s
    for k in keys:
        out = re.sub(r"(?:(?<=_)|^)" + re.escape(k) + r"(?=_|$)", names[k], out)
    return out

old_defs, old_decls, old_other = parse(old_path)
new_defs, new_decls, new_other = parse(new_path)

reach, todo = set(), [s for s in PUBLIC if s in old_defs]
while todo:
    f = todo.pop()
    if f in reach:
        continue
    reach.add(f)
    todo += [c for c in callees(old_defs[f]) if c in old_defs]

fails = 0
renamed = {rename_sym(f): f for f in reach}
if len(renamed) != len(reach):
    print("FAIL: the rename map collapses two reachable symbols")
    fails += 1
missing = sorted(set(renamed) - set(new_defs))
extra = sorted(set(new_defs) - set(renamed))
for m in missing:
    print(f"FAIL missing in isarri.ll: {m} (was {renamed[m]})")
for e in extra:
    print(f"FAIL extra define in isarri.ll: {e}")
fails += len(missing) + len(extra)

changed = 0
for new_name, old_name in sorted(renamed.items()):
    if new_name not in new_defs:
        continue
    body = SYM.sub(lambda m: "@" + rename_sym(m.group(1)), old_defs[old_name])
    if body != new_defs[new_name]:
        changed += 1
        print(f"FAIL body differs: {new_name}")
fails += changed

need_decls = {c for f in reach for c in callees(old_defs[f]) if c in old_decls}
for d in sorted(need_decls):
    if rename_sym(d) not in new_decls:
        print(f"FAIL missing declare: {d}")
        fails += 1

print(f"reachable in shipped: {len(reach)} of {len(old_defs)} defines; isarri.ll defines: {len(new_defs)}; "
      f"changed bodies: {changed}; renamed symbols: {sum(1 for n, o in renamed.items() if n != o)}")
print("PASS" if fails == 0 else f"FAIL ({fails})")
sys.exit(0 if fails == 0 else 1)

#!/usr/bin/env python3
"""Interval check for PARI's arm, whose ZX_Uspensky isolates the roots of the DEFLATED polynomial Q
(P = x^v Q(x^h)); for even h only the positive ones (each gives the two roots +-y^(1/h) of P).
The windows are checked against Q with Q's genuine Sturm sequence (scripts/b2/sturm_windows.gp red(),
the same reduction and cache as the other checks): PARI's h and v must equal the checker's own; each
window holds exactly one root of Q (closed reading; a root also returned as a point is not counted against a
window that ends at it, as check_risolate_windows.py --open; a point strictly inside a window is counted, since
2026-10-24: ZX_Uspensky returns a rational root as a point and leaves the window it lies in unshrunk); the union holds as many roots as there are windows; and the number of
windows equals the number of roots of Q that PARI is to return (all for odd h, the positive ones for even h).
Input: windows_<suite>_parisqf.tsv (name, idx, h, v, left, right). Output: <input>.check.tsv.
Usage: check_reduced_windows.py <suite> <windows.tsv> [--jobs N] [--budget S] | --selftest"""
import collections, concurrent.futures as cf, importlib.util, os, subprocess, sys
sys.set_int_max_str_digits(0)
REPO = os.path.expanduser("~/Desktop/Dsc_LLVM")
spec = importlib.util.spec_from_file_location("ck", f"{REPO}/scripts/b2/check_risolate_windows.py")
ck = importlib.util.module_from_spec(spec); spec.loader.exec_module(ck)
GPF = r"""
cq(S, Q, a, b) = openc(S, Q, a, b) + (subst(Q, 'x, a) == 0) + (a < b && subst(Q, 'x, b) == 0);
chkQ(name, idx, P, h, v, W) = {
  my(D = red(P), Q = D[3], S = D[4], d = D[2], tot, err = List(), iv, m, lo, hi, u = 0);
  if (d != h || D[1] != v, listput(err, Str("reduction:", h, ",", v, "/", d, ",", D[1])));
  tot = if (d % 2, Vinf(S, -1) - Vinf(S, 1), Vat(S, 0) - Vinf(S, 1));
  iv = W;
  for (i = 1, #iv,
    if (iv[i][1] > iv[i][2], listput(err, Str("reversed:", i)));
    if (d % 2 == 0 && iv[i][1] < 0, listput(err, Str("negative-side:", i)));
    m = cq(S, Q, iv[i][1], iv[i][2]);
    if (iv[i][1] < iv[i][2],
      m -= sum(j = 1, #iv, iv[j][1] == iv[j][2] && (iv[j][1] == iv[i][1] || iv[j][1] == iv[i][2]) && subst(Q, 'x, iv[j][1]) == 0));
    if (m != 1, listput(err, Str("window-holds:", i, ":", m, "/1"))));
  iv = vecsort(iv, 1); lo = 0; hi = 0;
  for (i = 1, #iv,
    if (i == 1, lo = iv[i][1]; hi = iv[i][2],
      if (iv[i][1] <= hi, hi = max(hi, iv[i][2]), u += cq(S, Q, lo, hi); lo = iv[i][1]; hi = iv[i][2])));
  if (#iv, u += cq(S, Q, lo, hi));
  if (u != #W, listput(err, Str("union-holds:", u, "/", #W)));
  if (#W != tot, listput(err, Str("count:", #W, "/", tot)));
  print(name, "\t", idx, "\t", if (#err, "FAIL", "OK"), "\t", tot, "\t", #W, "\t", strjoin(Vec(err), ","));
}
"""
def shard(a):
    items, budget = a
    prog = [f'read("{ck.GP}");', GPF] + ck.sturm_cache_lines()
    prog.append('one(n, i, P, h, v, W, nw) = my(r = iferr(alarm(%d, chkQ(n, i, P, h, v, W)), E, E)); '
                'if (type(r) == "t_ERROR", print(n, "\\t", i, "\\tUNCHECKED\\t-1\\t", nw, "\\t", errname(r)));' % budget)
    script = "\n".join(prog) + "\n" + "\n".join(
        f'CURKEY = "{ck.sturm_key(P)}"; one("{n}", {i}, {P}, {h}, {v}, {W}, {nw});' for n, i, P, h, v, W, nw in items) + "\n"
    r = subprocess.run(["gp", "-q", "--default", "parisizemax=8000000000"], input=script, capture_output=True, text=True)
    out = [l for l in r.stdout.splitlines() if l.count("\t") >= 4]
    if r.returncode != 0 and not out: out.append(f"SHARD-ERROR\t0\tUNCHECKED\t-1\t0\t{r.stderr.strip()[:200]}")
    return out
SELFTEST = [  # (name, windows as [left, right], expected) on P = (15x+4)(4x^2-1), roots -1/2, -4/15, 1/2
    ("points-and-windows", "[[-1,-1/3],[-4/15,-4/15],[0,1]]", "OK"),
    ("point-at-endpoint", "[[-1,-4/15],[-4/15,-4/15],[0,1]]", "OK"),
    ("point-strictly-inside", "[[-1,0],[-4/15,-4/15],[0,1]]", "FAIL"),   # PARI's output shape, 2026-10-24
]
def selftest():
    P = "(15*x+4)*(4*x^2-1)"          # roots -1/2, -4/15, 1/2; h = 1, v = 0
    prog = [f'read("{ck.GP}");', GPF, 'CURKEY = "";'] + [f'chkQ("{n}", 1, {P}, 1, 0, {w});' for n, w, _ in SELFTEST]
    r = subprocess.run(["gp", "-q"], input="\n".join(prog) + "\n", capture_output=True, text=True)
    got = {l.split("\t")[0]: l.split("\t")[2] for l in r.stdout.splitlines() if l.count("\t") >= 4}
    bad = [(n, want, got.get(n)) for n, _, want in SELFTEST if got.get(n) != want]
    print("selftest", "FAILED " + str(bad) if bad else f"OK ({len(SELFTEST)} cases)"); sys.exit(1 if bad else 0)
def main():
    if sys.argv[1:] == ["--selftest"]: selftest()
    suite, path = sys.argv[1:3]
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 6
    budget = int(sys.argv[sys.argv.index("--budget") + 1]) if "--budget" in sys.argv else 300
    SH = int(sys.argv[sys.argv.index("--shard") + 1]) if "--shard" in sys.argv else (4 if suite in ("mpsolve", "and", "ccluster") else 400)
    W = collections.defaultdict(set); hv = {}
    for line in open(path):
        n, i, h, v, l, r = line.rstrip("\n").split("\t")
        W[(n, int(i))].add((l, r)); hv.setdefault((n, int(i)), set()).add((h, v))
    cache, items = {}, []
    for (n, i) in sorted(W):
        assert len(hv[(n, i)]) == 1
        h, v = next(iter(hv[(n, i)])); ws = sorted(W[(n, i)])
        items.append((n, i, ck.poly_text(suite, n, i, cache), h, v, "[" + ",".join(f"[{l},{r}]" for l, r in ws) + "]", len(ws)))
    shards = [(items[k:k + SH], budget) for k in range(0, len(items), SH)]
    c = collections.Counter()
    with open(path + ".check.tsv", "w") as fo, cf.ProcessPoolExecutor(jobs) as ex:
        fo.write("name\tidx\tstatus\tsturm_total\tn_windows\treasons\n")
        for res in ex.map(shard, shards):
            for l in res: fo.write(l + "\n"); c[l.split("\t")[2]] += 1
            fo.flush()
    print(f"OK {c['OK']}  FAIL {c['FAIL']}  UNCHECKED {c['UNCHECKED']}  -> {path}.check.tsv")
if __name__ == "__main__":
    main()

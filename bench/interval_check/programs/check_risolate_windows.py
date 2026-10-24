#!/usr/bin/env python3
"""check_risolate_windows.py -- check Risolate's output intervals with genuine Sturm sequences
(docs/HELDOUT_PLAN_2026-09-29.md §E; the same functions as scripts/b2/sturm_windows.gp, not PARI's
polsturm, which is Uspensky's Descartes method).

  python3 scripts/b2/check_risolate_windows.py <suite> <windows.tsv> [--jobs N] [--budget S] [--only NAME]
  python3 scripts/b2/check_risolate_windows.py --selftest    (the --open reading on planted outputs)
     suite: mpsolve | smt | heldout | and | ccluster | logcfbench

The windows file is what risolate_bench appends after its timed region (RISOLATE_WINDOWS):
  <case or instance> \\t <poly index, 1-based> \\t <nSols> \\t <center> \\t <radius>   (exact rationals)
The tool's interval is the closed [center - radius, center + radius]. Repetitions of a deterministic
run repeat the same windows; they are de-duplicated per polynomial (a difference between reps would
show as extra windows and fail the count).
Per polynomial it verifies, with P's genuine Sturm sequence (squarefree input, certified per suite):
  every window holds exactly the number of roots Risolate claims for it (nSols; 1 for squarefree
  input); the windows' union holds exactly as many roots as there are windows, so no root lies in two
  windows; and the number of windows equals P's number of real roots (nothing missed).
A polynomial over the Sturm budget is reported UNCHECKED, never as passing. Output:
  <windows.tsv>.check.tsv   name idx status sturm_total n_windows reasons
A count check, not a timing: load-insensitive, but it loads the machine -- never run it beside a
measured job.
"""
import argparse
import collections
import concurrent.futures as cf
import hashlib
import os
import subprocess
import sys

sys.set_int_max_str_digits(0)
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
GP = os.path.join(REPO, "scripts/b2/sturm_windows.gp")

# Sturm-sequence cache (sturm_windows.gp red(); 2026-09-29): each sequence is saved as soon as it is built,
# before any root is counted, keyed by the sha256 of the polynomial's coefficient text, and reused on later
# runs after an exact check that it belongs to that polynomial. STURM_CACHE_DIR overrides the directory;
# STURM_CACHE_DIR=off disables it.
STURM_CACHE_DIR = os.environ.get("STURM_CACHE_DIR", os.path.join(REPO, "benchmark_results/sturm_cache"))


def sturm_cache_lines():
    if STURM_CACHE_DIR in ("", "off"):
        return []
    os.makedirs(STURM_CACHE_DIR, exist_ok=True)
    open(os.path.join(STURM_CACHE_DIR, ".metadata_never_index"), "a").close()
    return [f'STURM_CACHE = "{STURM_CACHE_DIR}";']


def sturm_key(text):
    return hashlib.sha256(text.encode()).hexdigest()
SRC = {
    "mpsolve": ("coeffs", os.path.join(REPO, "benchmark_results/mpsolve_suite/coeffs")),
    "and": ("coeffs", os.path.join(REPO, "benchmark_results/and_bench/coeffs")),
    "ccluster": ("coeffs", os.path.join(REPO, "benchmark_results/ccluster_suite/coeffs")),
    "logcfbench": ("coeffs", os.path.join(REPO, "benchmark_results/logcf_bench/coeffs")),
    "smt": ("apolys", os.path.join(REPO, "benchmark_results/smt_bench/extracted")),
    "heldout": ("apolys", os.path.join(REPO, "benchmark_results/smt_bench/heldout_2026-09-29/extracted")),
}

GP_FUNCS = r"""
closedc(D, P, a, b) = rootsP(D, a, b) + (subst(P, 'x, a) == 0) + (a < b && subst(P, 'x, b) == 0);
chkR(name, idx, P, W) = {
  my(D = red(P), S = D[4], tot, err = List(), I, iv, m, lo, hi, u = 0, k = 0);
  tot = (Vat(S, 0) - Vinf(S, 1)) + if (D[2] % 2, Vinf(S, -1) - Vat(S, 0), Vat(S, 0) - Vinf(S, 1)) + (D[1] == 1);
  iv = vector(#W, i, [W[i][1] - W[i][2], W[i][1] + W[i][2], W[i][3]]);
  for (i = 1, #iv, k += iv[i][3];
    if (iv[i][1] > iv[i][2], listput(err, Str("negative-radius:", i))));
  if (!OPENW,
    for (i = 1, #iv, m = closedc(D, P, iv[i][1], iv[i][2]);
      if (m != iv[i][3], listput(err, Str("window-holds:", i, ":", m, "/", iv[i][3])))),
    \\ endpoint reading (2026-10-09; strict since 2026-10-24): the polynomial passes if ONE end convention --
    \\ closed, open, [a,b) or (a,b] -- gives every window its claimed count; a root the tool also returned as
    \\ a point is not counted against a window that ENDS at it. A point strictly inside a window is counted:
    \\ that window holds two roots (x(x-1) with [0,0] and (-1,2) fails; until 2026-10-24 it passed).
    \\ The first failing window of the closed reading is reported.
    my(ok = 0, first = "", pts = select(w -> w[1] == w[2] && subst(P, 'x, w[1]) == 0, iv), cv = [[1,1],[0,0],[1,0],[0,1]]);
    for (c = 1, 4, my(bad = "");
      for (i = 1, #iv,
        if (iv[i][1] >= iv[i][2], m = closedc(D, P, iv[i][1], iv[i][2]),
          m = rootsP(D, iv[i][1], iv[i][2])
              + (cv[c][1] && subst(P, 'x, iv[i][1]) == 0 && !sum(j = 1, #pts, pts[j][1] == iv[i][1]))
              + (cv[c][2] && subst(P, 'x, iv[i][2]) == 0 && !sum(j = 1, #pts, pts[j][1] == iv[i][2])));
        if (m != iv[i][3] && bad == "", bad = Str("window-holds:", i, ":", m, "/", iv[i][3])));
      if (bad == "", ok = 1; break, if (c == 1, first = bad)));
    if (!ok, listput(err, first)));
  iv = vecsort(iv, 1);
  lo = 0; hi = 0;
  for (i = 1, #iv,
    if (i == 1, lo = iv[i][1]; hi = iv[i][2],
      if (iv[i][1] <= hi, hi = max(hi, iv[i][2]), u += closedc(D, P, lo, hi); lo = iv[i][1]; hi = iv[i][2])));
  if (#iv, u += closedc(D, P, lo, hi));
  if (u != k, listput(err, Str("union-holds:", u, "/", k)));
  if (k != tot, listput(err, Str("count:", k, "/", tot)));
  print(name, "\t", idx, "\t", if (#err, "FAIL", "OK"), "\t", tot, "\t", #W, "\t", strjoin(Vec(err), ","));
}
"""


def load_windows(path, only):
    W = collections.defaultdict(set)
    with open(path) as fh:
        for line in fh:
            p = line.rstrip("\n").split("\t")
            if len(p) != 5 or (only and p[0] != only):
                continue
            W[(p[0], int(p[1]))].add((p[3], p[4], int(p[2])))
    return W


def poly_text(suite, name, idx, cache):
    kind, d = SRC[suite]
    if kind == "coeffs":
        assert idx == 1, (name, idx)
        cs = open(os.path.join(d, name + ".txt")).read().strip()
    else:
        if name not in cache:
            lines = []
            with open(os.path.join(d, name + ".apolys")) as fh:
                for line in fh:
                    if line.startswith("A\t"):
                        lines.append(line.rstrip("\n").split("\t", 2)[2])
            cache.clear()
            cache[name] = lines
        cs = cache[name][idx - 1]
    return f"Polrev([{cs}], 'x)"


def run_shard(args):
    items, budget = args
    prog = [f'read("{GP}");', f"OPENW = {1 if os.environ.get('B2_OPEN_WINDOWS') == '1' else 0};", GP_FUNCS] + sturm_cache_lines()
    out = []
    # one gp per shard; every polynomial under its own alarm so one giant cannot eat the shard
    prog.append('one(n, i, P, W, nw) = my(r = iferr(alarm(%d, chkR(n, i, P, W)), E, E)); '
                'if (type(r) == "t_ERROR", print(n, "\\t", i, "\\tUNCHECKED\\t-1\\t", nw, "\\t", errname(r)));' % budget)
    script = "\n".join(prog) + "\n" + "\n".join(
        f'CURKEY = "{sturm_key(P)}"; one("{n}", {i}, {P}, {W}, {nw});' for n, i, P, W, nw in items) + "\n"
    r = subprocess.run(["gp", "-q", "--default", "parisizemax=8000000000"], input=script,
                       capture_output=True, text=True)
    for line in r.stdout.splitlines():
        if line.count("\t") >= 4:
            out.append(line)
    if r.returncode != 0 and not out:
        out.append(f"SHARD-ERROR\t0\tUNCHECKED\t-1\t0\t{r.stderr.strip()[:200]}")
    return out


SELFTEST = [  # (claimed windows on x(x-1) as centre, radius, count; expected status under --open)
    ("exact-points", "[[0,0,1],[1,0,1]]", "OK"),
    ("point-at-endpoint", "[[0,0,1],[1/2,1/2,1]]", "OK"),
    ("point-strictly-inside", "[[0,0,1],[1/2,3/2,1]]", "FAIL"),   # the 2026-10-24 review's counterexample
    ("two-roots-one-window", "[[1/2,1,1]]", "FAIL"),
]


def selftest():
    prog = [f'read("{GP}");', "OPENW = 1;", GP_FUNCS, 'CURKEY = "";'] + [
        f'chkR("{n}", 1, x*(x-1), {w});' for n, w, _ in SELFTEST]
    r = subprocess.run(["gp", "-q"], input="\n".join(prog) + "\n", capture_output=True, text=True)
    got = {l.split("\t")[0]: l.split("\t")[2] for l in r.stdout.splitlines() if l.count("\t") >= 4}
    bad = [(n, want, got.get(n)) for n, _, want in SELFTEST if got.get(n) != want]
    print("selftest", "FAILED " + str(bad) if bad else f"OK ({len(SELFTEST)} cases)")
    sys.exit(1 if bad else 0)


def main():
    if sys.argv[1:] == ["--selftest"]:
        selftest()
    ap = argparse.ArgumentParser()
    ap.add_argument("suite", choices=sorted(SRC))
    ap.add_argument("windows")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--budget", type=int, default=300)
    ap.add_argument("--only", default="")
    ap.add_argument("--open", action="store_true",
                    help="for a tool that returns exact roots as point intervals and lets a neighbouring interval "
                    "end at one (logcf): a non-degenerate interval is read as closed, and a root that the tool "
                    "also returned as a point is not counted against an interval that ends at it (a point strictly "
                    "inside an interval is counted). The union and count checks are unchanged. --selftest checks "
                    "this reading on planted outputs")
    ap.add_argument("--shard", type=int, default=400, help="polynomials per gp process")
    ap.add_argument("--out", default="", help="output file (default <windows>.check.tsv; set it with --only)")
    a = ap.parse_args()
    os.environ["B2_OPEN_WINDOWS"] = "1" if a.open else "0"   # the environment reaches the pool's workers; a global does not
    W = load_windows(a.windows, a.only)
    keys = sorted(W)
    cache, items = {}, []
    for n, i in keys:
        ws = sorted(W[(n, i)])
        wv = "[" + ",".join(f"[{c},{r},{k}]" for c, r, k in ws) + "]"
        items.append((n, i, poly_text(a.suite, n, i, cache), wv, len(ws)))
    shards = [(items[k:k + a.shard], a.budget) for k in range(0, len(items), a.shard)]
    print(f"# {len(items)} polynomials with windows, {len(shards)} shards, {a.jobs} jobs", file=sys.stderr)
    out_path = a.out or a.windows + ".check.tsv"
    if a.only and not a.out:
        sys.exit("--only needs --out (it would overwrite the full check file)")
    n_ok = n_fail = n_unc = 0
    with open(out_path, "w") as fo, cf.ProcessPoolExecutor(a.jobs) as ex:
        fo.write("name\tidx\tstatus\tsturm_total\tn_windows\treasons\n")
        for res in ex.map(run_shard, shards):
            for line in res:
                fo.write(line + "\n")
                st = line.split("\t")[2]
                n_ok += st == "OK"; n_fail += st == "FAIL"; n_unc += st == "UNCHECKED"
            fo.flush()
    print(f"OK {n_ok}  FAIL {n_fail}  UNCHECKED {n_unc}  -> {out_path}")


if __name__ == "__main__":
    main()

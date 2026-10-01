#!/usr/bin/env python3
"""B2 (Astra review, 2026-09-26): validate IsaRRI's returned WINDOWS, not only its counts, with an
independent Sturm-sequence checker (scripts/b2/sturm_windows.gp; genuine Sturm sequences, not
PARI's polsturm, which PARI implements with Uspensky's Descartes method).

  python3 scripts/b2/check_windows.py --selftest
  python3 scripts/b2/check_windows.py <suite> [--budget S] [--limit N]    suite: smt | mpsolve | and

The windows come from the PUBLIC export (IsaRRI/export/isarri.ll) via scripts/b2/window_dump.c,
run outside any timing with out_cap = number of coefficients. For MPSolve-Bench and AND-Bench only
the cases IsaRRI completed in campaign 2 are replayed (others returned nothing to check).
Per polynomial the checker verifies: point windows are exact roots; each open window holds exactly
one root; no root lies in two windows (overlaps in root-free gaps are allowed); window counts per
half equal the Sturm totals and the reported counts; the zero flag; the halves and the dyadic /
reflected decoding. Each polynomial has a Sturm budget (--budget seconds, parisizemax 4 GB); a
polynomial over budget is reported UNCHECKED, never as passing. The Sturm totals are also compared
with the reference counts the campaign scored against.
Writes benchmark_results/b2_windows/<suite>.tsv. A count check, not a timing: load-insensitive.
"""
import csv, hashlib, os, subprocess, sys, time, tempfile, re

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
B2 = os.path.join(REPO, "scripts/b2")
ISARRI = os.path.expanduser("~/Desktop/IsaRRI")
OUTDIR = os.path.join(REPO, "benchmark_results/b2_windows")
BIN = os.path.join(tempfile.gettempdir(), "b2_window_dump")
CAMP = os.path.join(REPO, "benchmark_results/data/thesis_campaign2_2026-09-18")


def build():
    gmp = subprocess.run(["brew", "--prefix", "gmp"], capture_output=True, text=True).stdout.strip() or "/opt/homebrew"
    subprocess.run(["clang", "-O2", "-w", f"-I{ISARRI}/export", f"-I{gmp}/include", f"{B2}/window_dump.c",
                    f"{ISARRI}/export/isarri.ll", f"{ISARRI}/runtime/lib_isabelle_llvm.c",
                    f"-L{gmp}/lib", "-lgmp", "-o", BIN], check=True)


def dump(path, timeout):
    r = subprocess.run([BIN, path], capture_output=True, text=True, timeout=timeout)
    polys, cur = [], None
    for line in r.stdout.splitlines():
        f = line.split()
        if f[0] == "P":
            cur = {"idx": int(f[1]), "pos": int(f[2]), "neg": int(f[3]), "xs0": int(f[4]), "w": [], "err": None}
            polys.append(cur)
        elif f[0] == "E":
            cur["err"] = "capacity"
        else:
            cur["w"].append((1 if f[0] == "+" else -1, f[1], f[2], f[3]))
    return polys


def read_coeffs(path):
    """[(idx, deg, coeff string)] in the numbering window_dump uses."""
    out, idx = [], 0
    for line in open(path):
        if line.startswith("A\t"):
            _, deg, cs = line.rstrip("\n").split("\t")
            idx += 1; out.append((idx, int(deg), cs))
        elif line[:1].isdigit() or line[:1] == "-":
            idx += 1; cs = line.strip(); out.append((idx, cs.count(","), cs))
    return out


def gp_check(items, budget):
    """items: [(key, coeffs, poly dict)] -> {key: (status, tp, tn, z, reasons, seconds)}"""
    lines = ['default(parisizemax, 2^32);', f'read("{B2}/sturm_windows.gp");']
    for key, cs, p in items:
        W = "[" + ",".join(f"[{s},{l},{r},{k}]" for s, l, r, k in p["w"]) + "]"
        # alarm() does not raise on timeout: it RETURNS a t_ERROR (e_ALARM), which iferr never sees.
        # Before 2026-09-27 such a timeout printed nothing and was labelled "gp-died".
        lines.append(f'my(t0=getabstime(), r); iferr(r = alarm({budget}, check("{key}", Pol(Vecrev([{cs}])), '
                     f'{p["pos"]}, {p["neg"]}, {p["xs0"]}, {W})); if(type(r) == "t_ERROR", '
                     f'print("{key}\\tUNCHECKED\\t-\\t-\\t-\\t", Str(errname(r)))), E, '
                     f'print("{key}\\tUNCHECKED\\t-\\t-\\t-\\t", Str(errname(E)))); '
                     f'print("T\\t{key}\\t", getabstime()-t0);')
    r = subprocess.run(["gp", "-q", "-D", "readline=0"], input="\n".join(lines) + "\n",
                       capture_output=True, text=True)
    res, secs = {}, {}
    for line in r.stdout.splitlines():
        f = line.split("\t")
        if f[0] == "T":
            secs[f[1].strip()] = int(f[2]) / 1000.0
        elif len(f) >= 5:
            res[f[0].strip()] = (f[1], f[2], f[3], f[4], f[5] if len(f) > 5 else "",
                                 f[6].strip() if len(f) > 6 else "-", f[7].strip() if len(f) > 7 else "-")
    for key, _, _ in items:
        if key not in res:
            res[key] = ("UNCHECKED", "-", "-", "-", "gp-died", "-", "-")
    return {k: (v + ("-", "-"))[:7] + (secs.get(k, -1),) for k, v in res.items()}


# ---------------------------------------------------------------- self-test on planted corruptions
def selftest():
    build()
    cases = {"ch6": "6,-5,-2,1", "x3m2x": "0,-2,0,1", "powsub": "4," + "0," * 11 + "-5," + "0," * 11 + "1",
             "wilk10": "3628800,-10628640,12753576,-8409500,3416930,-902055,157773,-18150,1320,-55,1",
             "mig": "-2," + "536870912,-36028797018963968" + ",0" * 13 + ",1",
             "odd-d9": "-2" + ",0" * 8 + ",1", "k1-d4": "0,-3,0,0,0,1"}
    tmp = tempfile.mkdtemp()
    items, real = [], {}
    for name, cs in cases.items():
        pth = os.path.join(tmp, name + ".txt"); open(pth, "w").write(cs + "\n")
        p = dump(pth, 60)[0]; real[name] = (cs, p)
        items.append((name, cs, p))
    def clone(p, w, **kw):
        q = dict(p); q.update(kw); q["w"] = w; return q
    cs, p = real["wilk10"]
    w = p["w"]; opens = [i for i, x in enumerate(w) if x[1] != x[2]]; pts = [i for i, x in enumerate(w) if x[1] == x[2]]
    o = opens[0]; o2 = opens[1]
    bad = {
        "dup-window": clone(p, w[:o2] + [w[o]] + w[o2 + 1:]),
        "exponent+1": clone(p, [(s, l, r, str(int(k) + 1)) if i == o else (s, l, r, k) for i, (s, l, r, k) in enumerate(w)]),
        "point-not-root": clone(p, [(s, l, l, k) if i == o else (s, l, r, k) for i, (s, l, r, k) in enumerate(w)]),
        "point-at-nonroot": clone(p, [(s, str(3 * int(l) + int(r)), str(3 * int(l) + int(r)), str(int(k) + 2)) if i == o else (s, l, r, k) for i, (s, l, r, k) in enumerate(w)]),
        "widened-over-root": clone(p, [(s, l, str(int(r) + (int(r) - int(l))), k) if i == o else (s, l, r, k) for i, (s, l, r, k) in enumerate(w)]),
    }
    cs6, p6 = real["ch6"]; w6 = p6["w"]
    bad["half-flip"] = clone(p6, [(-1,) + w6[0][1:]] + w6[1:], pos=p6["pos"] - 1, neg=p6["neg"] + 1)
    bad["reflection-unapplied"] = clone(p6, [(s, str(-int(r)), str(-int(l)), k) if s < 0 else (s, l, r, k) for s, l, r, k in w6])
    csx, px = real["x3m2x"]
    bad["zeroflag"] = clone(px, px["w"], xs0=1 - px["xs0"])
    bad["root-omitted-count-kept"] = clone(p, w[:o] + w[o + 1:] + [w[pts[0]]])
    for name, q in bad.items():
        items.append(("BAD-" + name, cs if name not in ("half-flip", "reflection-unapplied", "zeroflag") else
                      (cs6 if name != "zeroflag" else csx), q))
    res = gp_check(items, 60)
    ok = True
    for key, _, _ in items:
        st = res[key][0]
        want = "FAIL" if key.startswith("BAD-") else "OK"
        print(f"  {key:28s} {st:9s} {res[key][4]}")
        ok &= (st == want)
    if not ok:
        sys.exit("SELFTEST FAILED")
    print("selftest: every real output OK, every planted corruption FAIL")


# ---------------------------------------------------------------- suites
def cases(suite):
    if suite == "smt":
        ext = os.path.join(REPO, "benchmark_results/smt_bench/extracted")
        return [(f[:-7], os.path.join(ext, f), None) for f in sorted(os.listdir(ext)) if f.endswith(".apolys")]
    cap = 60000 if suite == "mpsolve" else 150000
    d = os.path.join(REPO, "benchmark_results", "mpsolve_suite/coeffs" if suite == "mpsolve" else "and_bench/coeffs")
    out = []
    for r in csv.DictReader(open(os.path.join(CAMP, f"{suite}_results.csv"))):
        if r["solver"] == "powsub_l4" and r["status"] == "OK" and (float(r["ms"]) <= cap or "--include-overcap" in sys.argv):
            out.append((r["case"], os.path.join(d, r["case"] + ".txt"), int(r["oracle"])))
    return out


def smt_oracle():
    ref = {}
    p = os.path.join(REPO, "benchmark_results/smt_bench/results/sturm_per_poly.tsv")
    for line in open(p):
        if not line.startswith("instance\t"):
            i, k, d, s = line.rstrip("\n").split("\t"); ref[(i, int(k))] = int(s)
    return ref


def run(suite, budget, limit):
    build()
    os.makedirs(OUTDIR, exist_ok=True)
    out = os.path.join(OUTDIR, f"{suite}.tsv" if "--out" not in sys.argv else sys.argv[sys.argv.index("--out") + 1])
    done = set()
    if os.path.exists(out):
        done = {l.split("\t")[0] for l in open(out) if not l.startswith("case\t")}
    fo = open(out, "a")
    export_sha = hashlib.sha256(open(f"{ISARRI}/export/isarri.ll", "rb").read()).hexdigest()[:16]
    commit = subprocess.run(["git", "-C", REPO, "rev-parse", "--short", "HEAD"], capture_output=True, text=True).stdout.strip()
    if subprocess.run(["git", "-C", REPO, "status", "--porcelain", "scripts/b2"], capture_output=True, text=True).stdout.strip():
        commit += "-dirty"
    if not done:
        fo.write("case\tpoly\tdeg\tinput_sha256\texport_sha16\tchecker\treported_pos\treported_neg\treported_zero\t"
                 "status\tsturm_pos\tsturm_neg\tzero\treduction_k\treduction_d\treference\tref_agree\treasons\tcheck_s\n")
    ref_smt = smt_oracle() if suite == "smt" else None
    only = set(sys.argv[sys.argv.index("--cases") + 1].split(",")) if "--cases" in sys.argv else None
    todo = [c for c in cases(suite) if c[0] not in done and (only is None or c[0] in only)][:limit]
    if "--shard" in sys.argv:
        i, n = map(int, sys.argv[sys.argv.index("--shard") + 1].split("/"))
        todo = todo[i::n]
    if "--reverse" in sys.argv:          # an extra worker taking the same list from the other end
        todo = todo[::-1]
    for n, (case, path, oracle) in enumerate(todo, 1):
        t0 = time.time()
        sha = hashlib.sha256(open(path, "rb").read()).hexdigest()
        try:
            polys = dump(path, int(sys.argv[sys.argv.index("--dump-timeout") + 1]) if "--dump-timeout" in sys.argv else 200)
        except subprocess.TimeoutExpired:
            fo.write(f"{case}\t-\t-\t{sha}\t{export_sha}\t{commit}\t-\t-\t-\tDUMP_TIMEOUT" + "\t-" * 9 + "\n"); fo.flush(); continue
        coeffs = {i: (d, cs) for i, d, cs in read_coeffs(path)}
        items = [(f"{case}#{p['idx']}", coeffs[p["idx"]][1], p) for p in polys]
        res = gp_check(items, budget)
        for p in polys:
            key = f"{case}#{p['idx']}"
            st, tp, tn, z, why, rk, rd, secs = res[key]
            if p["err"]:
                st, why = "FAIL", "capacity"
            if suite == "smt":
                refv = ref_smt.get((case, p["idx"]), "-")
            else:
                refv = oracle
            agree = "-"
            if st != "UNCHECKED" and refv not in ("-", -1):
                agree = int(int(tp) + int(tn) + int(z) == int(refv))
            fo.write(f"{case}\t{p['idx']}\t{coeffs[p['idx']][0]}\t{sha}\t{export_sha}\t{commit}\t{p['pos']}\t{p['neg']}\t{p['xs0']}\t"
                     f"{st}\t{tp}\t{tn}\t{z}\t{rk}\t{rd}\t{refv}\t{agree}\t{why}\t{secs}\n")
        fo.flush()
        print(f"[{n}/{len(todo)}] {case}: {len(polys)} poly, {time.time() - t0:.1f}s", flush=True)
    fo.close()


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        selftest(); sys.exit(0)
    suite = sys.argv[1]
    budget = int(sys.argv[sys.argv.index("--budget") + 1]) if "--budget" in sys.argv else 120
    limit = int(sys.argv[sys.argv.index("--limit") + 1]) if "--limit" in sys.argv else None
    run(suite, budget, limit)

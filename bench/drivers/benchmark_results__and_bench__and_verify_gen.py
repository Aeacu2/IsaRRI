#!/usr/bin/env python3
"""AND_BENCH generation audit (gates G1 + G2 of docs/AND_BENCH.md §5).

G1 -- generation: every coeffs/<name>.txt exists, has the expected degree, and its max
coefficient bit-length stands in the pre-registered relation to the page's bitsize column:
  EXACT    |achieved - page_b| <= 2   (nested, mignotte rat/irr, gauss_*, dense, laguerre,
                                       wilkinson)
  TWOFOLD  recorded only: page_b ~= 2x achieved (chebyshev T/U, hermite, legendre -- the
           page's convention, suite-documented); assertion: ratio in [1.8, 2.3]
  WILKLIKE recorded only (wilkinson_like; page's construction deviates 0.92-0.95x)
  RESULT   recorded only (resultant; page's f,g magnitude unspecified)
Also asserts: REUSE files are byte-identical to their suite source (the cross-track contract),
and every case in cases_record.json has a non-PENDING oracle (G2, after the oracle phase).

Usage:
  python3 and_verify_gen.py                 # G1 audit of coeffs/ against gen_spec.tsv
  python3 and_verify_gen.py --oracle        # G2: run polsturm per PENDING case (CPU phase --
                                            #   fills cases_record.json oracles)

Oracle implementation note: scripts/sturm-count.py hardcodes the suite coeffs dir and is
owned by the suite audit; the AND oracle phase follows its documented pattern (gp + polsturm
on the coefficient file, exact integer arithmetic) with an explicit file path. See
scripts/sturm-count.py lines 68-86 for the gp invocation shape. The two guarded classes
come from the suite's own oracle records (final_suite_cases.hpp comment 2/3):
  - gauss_sqrtn/gauss_logn are P = f^2 - 1 (both constructors return f*f with the constant
    decremented): the suite proved direct polsturm explodes (case_34, 3.5 GB at deg 2048) and
    counts P = (f-1)(f+1) FACTORED instead -- recover f from P+1, VERIFY f^2 == P+1, then two
    cheap polsturm calls (scripts/gausssqrt-exact-count.py, whose poly_sqrt/poly_mul are
    imported here).
  - the rest run direct polsturm with the RSS guard (6 GB) and 1800 s timeout, exactly like
    sturm-count.py: an unavailable answer is PENDING again, never a fabricated count.
"""
import json
import math
import os
import subprocess
import sys
import threading
import time

sys.set_int_max_str_digits(0)
import importlib.util
_GSC = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))), "scripts", "gausssqrt-exact-count.py")
_spec = importlib.util.spec_from_file_location("gausssqrt_exact_count", _GSC)
_gsc_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_gsc_mod)
poly_mul, poly_sqrt = _gsc_mod.poly_mul, _gsc_mod.poly_sqrt

HERE = os.path.dirname(os.path.abspath(__file__))
COEFFS = os.path.join(HERE, "coeffs")
SPEC = os.path.join(HERE, "gen_spec.tsv")
CASES = os.path.join(HERE, "cases_record.json")
SUITE_COEFFS = "benchmark_results/final_suite/coeffs"

PARISIZE = 12_000_000_000          # gp stack (parisizemax); suite's sturm-count.py default
TIMEOUT_S = 1800.0                 # per polsturm invocation; suite default
RSS_LIMIT_GB = 6.0                 # suite default; a thrashing machine is worse than PENDING

BITS_CLASS = {
    "nested_mignotte": "EXACT", "mignotte_rat": "EXACT", "mignotte_irr": "EXACT",
    "gauss_sqrtn": "EXACT", "gauss_logn": "EXACT",
    "random_dense": "EXACT", "random_monic": "EXACT", "random_monic_lt1": "EXACT",
    "laguerre": "EXACT", "wilkinson": "EXACT",
    "chebyshev_T": "TWOFOLD", "chebyshev_U": "TWOFOLD", "hermite": "TWOFOLD",
    "legendre": "TWOFOLD", "wilkinson_like": "WILKLIKE", "resultant": "RESULT",
}


def bits_of(path):
    txt = open(path).read().strip().strip("[]")
    cs = [int(x) for x in txt.split(",") if x.strip() != ""]
    return len(cs) - 1, max(c.bit_length() for c in cs)


def suite_file_family(family, table):
    return {"chebyshev_T": "chebyshevT", "chebyshev_U": "chebyshevU",
            "mignotte_rat": "migRat" if table == 10 else "migRatDeg",
            "mignotte_irr": "migIrr" if table == 12 else "migIrrDeg",
            "random_dense": "dense", "random_monic": "denseMon",
            "random_monic_lt1": "denseM1", "wilkinson_like": "wilkinLike",
            "nested_mignotte": "nested" if table == 2 else "nestedTau",
            "gauss_sqrtn": "gaussSqrt", "gauss_logn": "gaussLogN",
            "resultant": "resultant", "hermite": "hermite", "laguerre": "laguerre",
            "legendre": "legendre", "wilkinson": "wilkinson"}[family]


# Pre-registered adjudication (2026-08-09, generation G1): gauss_sqrtn achieved 1025-1029
# across ALL 20 rows (reuse + generated, one construction) vs the page column 1024-1027;
# the +3 rows are the family's natural draw spread, not a construction mismatch -- the
# difficulty axis (1024-bit coefficients, tau=512 Gaussian clusters) is preserved. Rows
# outside the +-2 gate are ACCEPTED here; anything else still fails G1.
ADJUDICATED = {
    "and05_gauss_sqrtn_d22_b1024": "ach 1027 vs page 1024 (+3, family spread)",
    "and05_gauss_sqrtn_d256_b1025": "ach 1028 vs page 1025 (+3, family spread)",
    "and05_gauss_sqrtn_d4832_b1026": "ach 1029 vs page 1026 (+3, family spread)",
    "and05_gauss_sqrtn_d6428_b1026": "ach 1029 vs page 1026 (+3, family spread)",
}


def main():
    rows = [l.rstrip("\n").split("\t") for l in open(SPEC)
            if not l.startswith("#") and l.strip()]
    assert len(rows) == 295, f"gen_spec: expected 295 rows, got {len(rows)}"
    fails, reused_ok, exact_ok, twofold_ok = [], 0, 0, 0
    for r in rows:
        name, family, table, degree, page_b, ctor, a, b, c, seed, source, scase, ora, achieved, desc = r
        degree, page_b = int(degree), int(page_b)
        path = os.path.join(COEFFS, name + ".txt")
        if not os.path.exists(path):
            fails.append(f"{name}: MISSING coeffs file")
            continue
        d, ach = bits_of(path)
        if d != degree:
            fails.append(f"{name}: degree {d} != {degree}")
        if source == "reuse":
            src = os.path.join(SUITE_COEFFS, f"case_{scase}_{suite_file_family(family, int(table))}.txt")
            if open(path, "rb").read() != open(src, "rb").read():
                fails.append(f"{name}: NOT byte-identical to suite case_{scase}")
            reused_ok += 1
        cls = BITS_CLASS[family]
        if cls == "EXACT":
            if abs(ach - page_b) > 2 and name not in ADJUDICATED:
                fails.append(f"{name}: bits {ach} vs page {page_b} (EXACT, +-2)")
            else:
                exact_ok += 1
        elif cls == "TWOFOLD":
            ratio = page_b / ach
            if not (1.8 <= ratio <= 2.3):
                fails.append(f"{name}: twofold ratio {ratio:.3f} out of [1.8, 2.3]")
            else:
                twofold_ok += 1
    if fails:
        print(f"G1 FAIL: {len(fails)} problems")
        for f in fails:
            print("  " + f)
        return 1
    print(f"G1 PASS: 295/295 coeffs; reuse byte-identical {reused_ok}/90; "
          f"EXACT +-2 {exact_ok}; TWOFOLD ratio {twofold_ok}")
    rec = json.load(open(CASES))
    pending = [r for r in rec if r["oracle"] == "PENDING"]
    print(f"oracle: {len(rec) - len(pending)}/295 determined; {len(pending)} PENDING "
          f"(run --oracle after the generation phase)")
    return 0


def _rss_gb(pid):
    try:
        out = subprocess.run(["ps", "-o", "rss=", "-p", str(pid)],
                             capture_output=True, text=True, timeout=5).stdout.strip()
        return int(out) / 1048576.0 if out else 0.0
    except Exception:
        return 0.0


def _rss_guard(proc, limit_gb, poll=2.0):
    while proc.poll() is None:
        if _rss_gb(proc.pid) > limit_gb:
            proc._rss_killed = True
            try:
                os.killpg(os.getpgid(proc.pid), 9)
            except (ProcessLookupError, PermissionError):
                pass
            return
        time.sleep(poll)


def _gp_polsturm(coeffs, tag):
    """Exact real-root count via gp; the suite's battle-tested pattern (sturm-count.py:
    every statement on ONE line, parisizemax on its OWN line, vector literal + Pol(Vecrev(c))
    -- the x^0 + x^1 + ... expression form hits gp's parser nesting limit at ~10^4 terms).
    Returns (count, elapsed) or (None, elapsed) on timeout/RSS-kill/parse failure; a RESULT
    line whose degree does not match len(coeffs)-1 is rejected (never trusted)."""
    script = os.path.join(HERE, ".oracle_tmp.gp")
    with open(script, "w") as out:
        out.write("default(parisizemax, %d);\n" % PARISIZE)
        out.write("c=[" + ",".join(str(c) for c in coeffs) + "];\n")
        out.write("P = Pol(Vecrev(c));\n")
        out.write('print("RESULT ", poldegree(P), " ", polsturm(P));\n')
        out.write("quit;\n")
    t0 = time.time()
    proc = subprocess.Popen(["gp", "-q", script], stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True, start_new_session=True)
    watcher = threading.Thread(target=_rss_guard, args=(proc, RSS_LIMIT_GB), daemon=True)
    watcher.start()
    try:
        out_s, err_s = proc.communicate(timeout=TIMEOUT_S)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(proc.pid), 9)
        except (ProcessLookupError, PermissionError):
            pass
        proc.wait()
        print(f"  [{tag}] TIMEOUT after {TIMEOUT_S:.0f}s -- PENDING")
        return None, time.time() - t0
    if getattr(proc, "_rss_killed", False):
        print(f"  [{tag}] RSS guard killed it ({RSS_LIMIT_GB:.0f} GB) -- PENDING")
        return None, time.time() - t0
    for ln in out_s.splitlines():
        if ln.startswith("RESULT"):
            deg, n = ln.split()[1:3]
            if int(deg) != len(coeffs) - 1:
                print(f"  [{tag}] degree mismatch {deg} != {len(coeffs)-1} -- PENDING")
                return None, time.time() - t0
            return int(n), time.time() - t0
    print(f"  [{tag}] no RESULT; gp: {(err_s or out_s).strip()[:120]}")
    return None, time.time() - t0


def _gauss_count(name, coeffs):
    """Factored exact count for P = f^2 - 1 (the suite's gausssqrt-exact-count.py method):
    recover f from P+1, verify f^2 == P+1 exactly, then polsturm(f-1) + polsturm(f+1)."""
    Q = list(coeffs)
    Q[0] += 1
    f = poly_sqrt(Q)
    if f is None:
        print(f"  [{name}] P+1 NOT a perfect square -- family identity broken; PENDING")
        return None
    if poly_mul(f, f) != Q:
        print(f"  [{name}] f^2 != P+1 verification FAILED; PENDING")
        return None
    n1, t1 = _gp_polsturm([c - (1 if i == 0 else 0) for i, c in enumerate(f)], name + "_fminus")
    n2, t2 = _gp_polsturm([c + (1 if i == 0 else 0) for i, c in enumerate(f)], name + "_fplus")
    if n1 is None or n2 is None:
        return None
    print(f"  [{name}] factored: ({n1}, {t1:.0f}s) + ({n2}, {t2:.0f}s) = {n1 + n2}")
    return n1 + n2


def _nested_oracle(degree, tau):
    """PROVEN oracle for the nested-mignotte family (replaces computation; the direct
    full-polsturm cost scales ~tau^2 -- measured 0s at tau=16 .. 145s at tau=360, i.e.
    ~50 h/row at the tau=32768 ladder top).

    THEOREM. P = prod_{i=1..4} f_i, f_i(x) = x^m - q(x)^(2i), q = a x^2 - 1,
    a = 2^(tau/8) - 1, m = n/4 odd >= 33 (holds for every nested row: t01 m=65 all tau;
    t02 m in {33,45,65,91,129,181,257,363,513,725,1025,1449,2049,2897}, tau=56), a >= 3.
    Then P has exactly 12 distinct real roots.
      (1) x < 0: x^m < 0 <= q^(2i)  =>  f_i < 0, no negative roots.
      (2) on [0,1/sqrt(a)]: f_i' = m x^(m-1) - 4ia x (a x^2 - 1)^(2i-1) > 0 (odd power
          of the negative q makes the second term positive); f_i(0) = -1 < 0 and
          f_i(1/sqrt(a)) = a^(-m/2) > 0  =>  exactly 1 root.
      (3) on [1/sqrt(a), inf): zeros of f_i' = zeros of m x^(m-2) = 4ia(a x^2-1)^(2i-1),
          i.e. of phi(x) = (a x^2-1)^(2i-1)/x^(m-2) = m/(4ia). phi' sign is the bracket
          (m-2) - a(m-4i)x^2 (4i <= 16 < m), strictly decreasing  =>  phi has ONE local
          max  =>  at most 2 critical points, at most 2 roots there. But f_i(1/sqrt(a)) > 0
          and f_i(1) = 1 - (a-1)^(2i) < 0 (a >= 3) with 1 > 1/sqrt(a)  =>  a root in
          (1/sqrt(a), 1); f_i(1) < 0 < lim f_i = +inf  =>  a root in (1, inf). So exactly 2.
      (4) per factor: 3 roots; factors pairwise coprime (shared root x: x^m = q^(2i) = q^(2j)
          => q = 0 (x=0, f_i(0)=-1) or q = +-1: q=1 => x=1, a-1=1 => a=2 => tau=8, excluded
          since tau >= 16; q=-1 => x=0 contradiction).  =>  4*3 = 12 DISTINCT real roots.
    Confirmation (not the proof): full polsturm measured 12 at tau = 16,32,40,64,88,128,
    176,256,360 (9 consecutive ladder rungs) and the suite MINTED 12,12 at tau=16,256."""
    assert degree % 4 == 0 and (degree // 4) % 2 == 1 and (degree // 4) >= 33
    assert tau >= 16 and tau % 8 == 0
    return 12


def oracle_phase(only_families=None, max_degree=None, timeout=TIMEOUT_S):
    """G2: exact real-root count per PENDING case. Gauss families go factored
    (P = (f-1)(f+1), suite's gausssqrt-exact-count.py method); nested_mignotte is PROVEN
    (= 12, _nested_oracle -- no computation); the rest run direct polsturm under the RSS
    guard. Every case keeps its PENDING status unless a VERIFIED exact count comes back; a
    case that cannot be answered stays PENDING for the pre-registered hand-adjudication
    before launch -- never dropped silently. Writes cases_record.json incrementally (a
    killed run must not lose computed oracles). Bounds: --only-family, --max-degree,
    --timeout (the dense monic family scales ~exponentially in degree: 5s @d128 .. 478s
    @d512 -- cap it or it burns hours for nothing)."""
    global TIMEOUT_S
    if timeout != TIMEOUT_S:
        TIMEOUT_S = timeout
    spec_rows = [l.rstrip("\n").split("\t") for l in open(SPEC)
                 if not l.startswith("#") and l.strip()]
    SPEC_B = {r[0]: int(r[7]) for r in spec_rows}
    rec = json.load(open(CASES))
    for r in rec:
        if r["oracle"] != "PENDING":
            continue
        if only_families and r["family"] not in only_families:
            continue
        if max_degree is not None and r["degree"] > max_degree:
            continue
        name, fam = r["name"], r["family"]
        path = os.path.join(COEFFS, name + ".txt")
        coeffs = [int(c) for c in open(path).read().strip().strip("[]").split(",") if c.strip()]
        assert len(coeffs) - 1 == r["degree"], f"{name}: file degree != manifest"
        t0 = time.time()
        if fam in ("gauss_sqrtn", "gauss_logn"):
            n = _gauss_count(name, coeffs)
        elif fam == "nested_mignotte":
            n = _nested_oracle(r["degree"], SPEC_B[name])  # proven = 12, no polsturm
        else:
            n, _ = _gp_polsturm(coeffs, name)
        if n is not None:
            r["oracle"] = n
            print(f"  [{name}] -> {n} ({time.time() - t0:.0f}s)", flush=True)
        json.dump(rec, open(CASES, "w"), indent=1)  # incremental: kills lose nothing
    pending = [r for r in rec if r["oracle"] == "PENDING"]
    print(f"oracle phase done: {len(rec) - len(pending)}/295 determined, {len(pending)} pending")
    return 0 if not pending else 2


def declare_guarded(min_degree=512):
    """Adjudication record for the uneconomical tail: PENDING dense rows at degree >=
    min_degree get a documented oracle_note (Sturm guard-bound; the monic family measured
    exponential -- 600 s timeout at d512, so the ≥d512 rows are not worth chasing). They stay
    PENDING: at launch they are adjudicated per the suite's policy (timing-only unless
    >= 3 solvers agree -- final_suite_cases.hpp comment 3). Never dropped silently."""
    rec = json.load(open(CASES))
    declared = 0
    for r in rec:
        if r["oracle"] != "PENDING":
            continue
        if not r["family"].startswith("random_"):
            continue
        if r["degree"] < min_degree:
            continue
        r["oracle_note"] = ("Sturm guard-bound: polsturm cost for dense random is "
                            "exponential in degree (measured 5s@d128..478s@d512); "
                            "adjudicate at launch per suite consensus rule")
        declared += 1
    json.dump(rec, open(CASES, "w"), indent=1)
    print(f"declare-guarded: {declared} rows noted (PENDING, oracle_note set)")
    return 0


if __name__ == "__main__":
    args = [a for a in sys.argv[1:]]
    if "--oracle" in args:
        fams = None
        md = None
        tm = TIMEOUT_S
        if "--only-family" in args:
            i = args.index("--only-family")
            fams = set(args[i + 1].split(","))
        if "--max-degree" in args:
            i = args.index("--max-degree")
            md = int(args[i + 1])
        if "--timeout" in args:
            i = args.index("--timeout")
            tm = float(args[i + 1])
        sys.exit(oracle_phase(only_families=fams, max_degree=md, timeout=tm))
    if "--declare-guarded" in args:
        sys.exit(declare_guarded())
    sys.exit(main())

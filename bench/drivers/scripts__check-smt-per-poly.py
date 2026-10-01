#!/usr/bin/env python3
"""Per-polynomial SMT-Bench count check: every arm's recorded count for every polynomial against
an independent Sturm count (PARI polsturm) of that polynomial.

  python3 scripts/check-smt-per-poly.py [--selftest] [--reuse-sturm]

Why: check-smt-sturm.py Sturm-counts every polynomial but keeps only instance TOTALS, and the
campaign scored competitors on instance totals, so two miscounts of opposite sign on different
polynomials of one instance would cancel. The runner already recorded one row per polynomial per
(arm, rep) in results/campaign2_run1_polys.tsv ("instance arm rep poly deg roots ms").

Matching: every arm reads the same extracted/<instance>.apolys and numbers the "A" lines in file
order from 1; the Sturm pass numbers them the same way. A row is matched by (instance, poly index)
and must also agree on the degree, which catches a misaligned numbering. Reported per arm:
rows, agree, count mismatch, degree mismatch (alignment failure), duplicate (instance, rep, poly)
rows, rows naming an unknown polynomial, and polynomials with no row at all (the arm did not
finish that instance in any rep, or crashed before printing). A count, not a timing:
load-insensitive. Writes results/sturm_per_poly.tsv (the oracle) and
results/per_poly_check.tsv (per-arm summary) plus results/per_poly_mismatches.tsv.
"""
import collections, os, subprocess, sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SB = f"{REPO}/benchmark_results/smt_bench"
EXT = f"{SB}/extracted"
POLYS = f"{SB}/results/campaign2_run1_polys.tsv"
ORACLE = f"{SB}/results/sturm_per_poly.tsv"
# --genuine-sturm: use the genuine Sturm-sequence counts of scripts/b2 (benchmark_results/b2_windows/smt.tsv,
# columns sturm_pos + sturm_neg + zero) instead of PARI's polsturm (which is Uspensky's Descartes method)
GENUINE = f"{REPO}/benchmark_results/b2_windows/smt.tsv"
SUMMARY = f"{SB}/results/per_poly_check.tsv"
MISMATCH = f"{SB}/results/per_poly_mismatches.tsv"


def read_inputs():
    """{(instance, idx): (deg, coeffs)} in the numbering every arm uses."""
    polys = {}
    for fn in sorted(os.listdir(EXT)):
        if not fn.endswith(".apolys"):
            continue
        inst = fn[: -len(".apolys")]
        idx = 0
        for line in open(f"{EXT}/{fn}"):
            f = line.rstrip("\n").split("\t")
            if len(f) != 3 or f[0] != "A":
                continue
            idx += 1
            polys[(inst, idx)] = (int(f[1]), f[2])
    return polys


def sturm_counts(polys):
    keys = sorted(polys)
    script = ["default(parisizemax, 2^30);"]
    for k in keys:
        script.append(f"print(polsturm(Pol(Vecrev([{polys[k][1]}]))));")
    r = subprocess.run(["gp", "-q", "-D", "readline=0"], input="\n".join(script) + "\n",
                       text=True, capture_output=True, check=True)
    out = r.stdout.split()
    if len(out) != len(keys):
        sys.exit(f"gp printed {len(out)} counts for {len(keys)} polynomials")
    with open(ORACLE, "w") as fo:
        fo.write("instance\tpoly\tdeg\tsturm\n")
        for k, s in zip(keys, out):
            fo.write(f"{k[0]}\t{k[1]}\t{polys[k][0]}\t{int(s)}\n")
    return {k: (polys[k][0], int(s)) for k, s in zip(keys, out)}


def load_oracle():
    ref = {}
    for line in open(ORACLE):
        if line.startswith("instance\t"):
            continue
        inst, idx, deg, s = line.rstrip("\n").split("\t")
        ref[(inst, int(idx))] = (int(deg), int(s))
    return ref


def compare(ref, rows):
    """ref: {(inst, idx): (deg, sturm)}; rows: iterable of (inst, arm, rep, idx, deg, roots).
    Returns ({arm: Counter}, [mismatch rows])."""
    stats = collections.defaultdict(collections.Counter)
    seen = collections.defaultdict(set)      # arm -> {(inst, idx)} with >= 1 row
    keyseen = set()
    bad = []
    for inst, arm, rep, idx, deg, roots in rows:
        st = stats[arm]
        st["rows"] += 1
        k3 = (arm, inst, rep, idx)
        if k3 in keyseen:
            st["duplicate"] += 1
            continue
        keyseen.add(k3)
        r = ref.get((inst, idx))
        if r is None:
            st["unknown_poly"] += 1
            bad.append((inst, arm, rep, idx, deg, roots, "unknown"))
            continue
        seen[arm].add((inst, idx))
        if r[0] != deg:
            st["deg_mismatch"] += 1
            bad.append((inst, arm, rep, idx, deg, roots, f"deg {r[0]}"))
        elif r[1] != roots:
            st["count_mismatch"] += 1
            bad.append((inst, arm, rep, idx, deg, roots, f"sturm {r[1]}"))
        else:
            st["agree"] += 1
    for arm in stats:
        stats[arm]["polys_covered"] = len(seen[arm])
        stats[arm]["polys_never_recorded"] = len(ref) - len(seen[arm])
    return stats, bad


def stream_rows():
    for line in open(POLYS):
        if line.startswith("#"):
            continue
        f = line.rstrip("\n").split("\t")
        if len(f) < 6 or f[1] == "arm":
            continue
        try:
            yield f[0], f[1], f[2], int(f[3]), int(f[4]), int(f[5])
        except ValueError:
            yield f[0], f[1], f[2], -1, -1, -1   # counted as unknown_poly


def selftest():
    ref = {("i", 1): (2, 2), ("i", 2): (3, 1), ("j", 1): (1, 1)}
    rows = [("i", "good", "1", 1, 2, 2), ("i", "good", "1", 2, 3, 1), ("j", "good", "1", 1, 1, 1),
            # cancelling pair: instance total correct (3), both polynomials wrong
            ("i", "cancel", "1", 1, 2, 1), ("i", "cancel", "1", 2, 3, 2),
            ("i", "shift", "1", 1, 3, 1),          # misaligned numbering
            ("i", "dup", "1", 1, 2, 2), ("i", "dup", "1", 1, 2, 2),
            ("x", "ghost", "1", 9, 1, 0)]
    st, bad = compare(ref, rows)
    checks = [st["good"]["agree"] == 3 and st["good"]["polys_never_recorded"] == 0,
              st["cancel"]["count_mismatch"] == 2,
              st["shift"]["deg_mismatch"] == 1 and st["shift"]["polys_never_recorded"] == 2,
              st["dup"]["duplicate"] == 1 and st["dup"]["agree"] == 1,
              st["ghost"]["unknown_poly"] == 1, len(bad) == 4]
    if not all(checks):
        sys.exit(f"SELFTEST FAILED: {checks}")
    print("selftest: planted cancelling pair, misalignment, duplicate and unknown row all detected")


def main():
    selftest()
    if "--selftest" in sys.argv:
        return 0
    if "--genuine-sturm" in sys.argv:
        ref, deg = {}, {k: v[0] for k, v in read_inputs().items()}
        for line in open(GENUINE):
            if line.startswith("case\t"):
                continue
            f = line.rstrip("\n").split("\t")
            if f[3] in ("OK", "FAIL"):
                ref[(f[0], int(f[1]))] = (deg[(f[0], int(f[1]))], int(f[4]) + int(f[5]) + int(f[6]))
        global SUMMARY, MISMATCH
        SUMMARY = SUMMARY.replace("per_poly_check", "per_poly_check_genuine_sturm")
        MISMATCH = MISMATCH.replace("per_poly_mismatches", "per_poly_mismatches_genuine_sturm")
    elif "--reuse-sturm" in sys.argv and os.path.exists(ORACLE):
        ref = load_oracle()
    else:
        ref = sturm_counts(read_inputs())
    print(f"oracle: {len(ref)} polynomials")
    stats, bad = compare(ref, stream_rows())
    cols = ["rows", "agree", "count_mismatch", "deg_mismatch", "duplicate", "unknown_poly",
            "polys_covered", "polys_never_recorded"]
    with open(SUMMARY, "w") as fo:
        fo.write("arm\t" + "\t".join(cols) + "\n")
        for arm in sorted(stats):
            fo.write(arm + "\t" + "\t".join(str(stats[arm][c]) for c in cols) + "\n")
    with open(MISMATCH, "w") as fo:
        fo.write("instance\tarm\trep\tpoly\tdeg\troots\treason\n")
        for b in bad:
            fo.write("\t".join(map(str, b)) + "\n")
    print(open(SUMMARY).read())
    print(f"wrote {SUMMARY}, {MISMATCH} ({len(bad)} rows)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

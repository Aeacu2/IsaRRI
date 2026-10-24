#!/usr/bin/env python3
"""Re-score SMT-Bench, the SMT held-out suite and MPSolve-Bench under the rule of 8 October 2026
(docs/LOGCF_PLAN_2026-10-08.md section 8): a wrong answer is a wrong count OR a checked output whose
intervals do not isolate the roots. Scoring is the campaign's (thesis notes/tools/eval_tables.py);
a completed cell of an arm whose interval check FAILs on that case (any polynomial of the instance) is
charged 2 x cap. IsaRRI and RisolateR: checked earlier, no failure (benchmark_results/b2_windows,
heldout_2026-09-29). ANewDsc -i 0 is the reference row; its intervals were not dumped.
Usage: apply_rule.py   (prints by-count and by-rule PAR2 and ranks, writes rule_scores.json)"""
import collections, csv, importlib.util, json, os
HOME = os.path.expanduser("~"); HERE = os.path.dirname(os.path.abspath(__file__))
L = f"{HOME}/Desktop/Dsc_LLVM/benchmark_results/data/logcf_2026-10-08"
spec = importlib.util.spec_from_file_location("et", f"{HOME}/Desktop/Thesis/notes/tools/eval_tables.py")
et = importlib.util.module_from_spec(spec); spec.loader.exec_module(et)
CHK = {"msolve": "msolve", "z3": "z3sqf", "libpoly": "libpolysqf", "cgal": "cgal", "sage": "sagesqf",
       "pari": "parisqf", "anewdsc": "anewdsc", "logcf": "logcf"}
# Not logcf's failure: in the timed session the instance before it was stopped at the cap while its
# intervals were being written, and this instance's first line was lost. Dumped again on its own, all
# 33 of its polynomials with roots pass (9 October 2026).
ARTEFACT = {("smt", "logcf", "QF_NIA_AProVE__aproveSMT6744620754635880037.smt2")}
def fails(suite, arm):
    p = f"{HERE}/windows_{suite}_{CHK[arm]}.tsv.check.tsv"
    f = collections.Counter(); u = set()
    for r in csv.DictReader(open(p), delimiter="\t"):
        if (suite, arm, r["name"]) in ARTEFACT: continue
        if r["status"] == "FAIL": f[r["name"]] += 1
        elif r["status"] == "UNCHECKED": u.add(r["name"])
    return f, u
out = {}
def report(suite, unit, cells, cap):
    """cells: {arm: {case: ms or None}}"""
    n = len(next(iter(cells.values()))); rows = {}
    for a, cl in cells.items():
        assert len(cl) == n, (suite, a, len(cl))
        par = lambda c: sum(v if v is not None and v <= cap else 2 * cap for v in c.values()) / n
        f, u = fails(suite, a) if a in CHK else ({}, set())
        hit = sorted(k for k in f if cl.get(k) is not None and cl[k] <= cap)
        c2 = dict(cl); [c2.__setitem__(k, None) for k in hit]
        rows[a] = dict(count=par(cl), rule=par(c2), charged=hit, fail_cases=len(f), unchecked=len(u))
    rk = lambda key: {a: i + 1 for i, a in enumerate(sorted((a for a in rows if a != "anewdsc_i0"), key=lambda a: rows[a][key]))}
    r1, r2 = rk("count"), rk("rule"); div = 1000 if unit == "s" else 1
    print(f"\n{suite}: {n} cases, PAR2 in {unit}")
    for a in sorted(rows, key=lambda a: (a == "anewdsc_i0", rows[a]["rule"])):
        r = rows[a]
        print(f"  {a:11s} by count {r['count']/div:9.3f} (#{r1.get(a, '-')})   by rule {r['rule']/div:9.3f} (#{r2.get(a, '-')})   "
              f"newly charged {len(r['charged'])}, failing cases {r['fail_cases']}, cases with an undecided polynomial {r['unchecked']}"
              + (f"  {r['charged']}" if 0 < len(r['charged']) <= 6 else ""))
        r["rank_count"], r["rank_rule"] = r1.get(a), r2.get(a)
    out[suite] = rows
# SMT sets
for suite, ref, ris in (("smt", et.SMT2, "smt"), ("heldout", et.HELDOUT, "heldout")):
    et.CAMPAIGN["smt"] = 2
    rows = et.read_smt_tsv(ref)
    z3ok = {x["instance"] for x in rows if x["arm"] == "z3" and x["status"] == "OK"}
    rows = [x for x in rows if x["instance"] in z3ok]
    n = len(z3ok)
    rows += [x for x in et.risolate_rows(ris, et.N_CASES["smt"] if suite == "smt" else et.N_HELDOUT, 5) if x["instance"] in z3ok]
    rows += [x for x in et.read_smt_tsv(f"{L}/{suite}/logcf_anchor_run1.tsv") if x["arm"] == "logcf" and x["instance"] in z3ok]
    et.ARMS = sorted({x["arm"] for x in rows})
    _, res = et.score_smt(rows)
    report(suite, "ms", {a: res[a]["cell"] for a in et.ARMS}, 1000.0)
# MPSolve-Bench
C = et.CAP2["mpsolve"]
def load(p):
    rows = list(csv.DictReader(open(p, newline="")))
    for x in rows: x["solver"] = et.RENAME2.get(x["solver"], x["solver"])
    return rows
rows = load(f"{et.DEV2}/mpsolve_results.csv") + [x for x in load(et.RIS["mpsolve"]) if x["solver"] == "risolate"] \
    + [x for x in load(f"{L}/mpsolve_logcf_anchor.csv") if x["solver"] == "logcf"]
cells = collections.defaultdict(dict)
for x in rows: cells[x["solver"]][x["case"]] = float(x["ms"]) if et.cell_ok(x) else None
report("mpsolve", "s", cells, C)
json.dump(out, open(f"{HERE}/rule_scores.json", "w"), indent=1)
# every failing (suite, isolator, case), for the thesis tables (eval_tables.py) and score_ccluster.py;
# AND-Bench and the Ccluster suite are included once their (partial) checks exist
with open(f"{HERE}/interval_failures.tsv", "w") as fo:
    fo.write("suite\tisolator\tcase\tfailing_polynomials\n")
    for suite in ("smt", "heldout", "mpsolve", "and", "ccluster", "logcfbench"):
        for a in sorted(CHK):
            if os.path.exists(f"{HERE}/windows_{suite}_{CHK[a]}.tsv.check.tsv"):
                for k, v in sorted(fails(suite, a)[0].items()):
                    fo.write(f"{suite}\t{a}\t{k}\t{v}\n")

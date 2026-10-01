#!/usr/bin/env python3
"""One manifest of the AND-Bench reference status (Astra review, 2026-09-26): every thesis statement
about which AND-Bench counts are settled, agreed or unchecked is generated from this file.

  python3 scripts/b2/and_reference_status.py

Per case, from campaign 2's and_results.csv (every run that returned a count, whatever its time):
  settled   the arms disagree (or an arm differed from the count used for scoring); the count is
            settled in benchmark_results/b2_windows/and_disputes.tsv (Sturm / theorem / certificate)
  agree     at least two different tools return a count and all counts agree
  one-tool  only one tool returns a count (ANewDsc's two configurations are one tool)
  none      no arm returns a count
Per arm, its credited completions in each category, computed with the thesis scorer's own rules
(eval_tables.py: rescore at the 150 s cap, replaying the ladder skip; cell_ok) so the numbers match
Table 7.5 exactly (an earlier version ignored the replayed ladder skip and counted 238, not 237,
for ANewDsc -i 0).
Writes benchmark_results/b2_windows/and_reference_status.tsv (per case) and prints the summary.
"""
import collections, csv, importlib.util, os

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CSV = os.path.join(REPO, "benchmark_results/data/thesis_campaign2_2026-09-18/and_results.csv")
OUT = os.path.join(REPO, "benchmark_results/b2_windows/and_reference_status.tsv")
CAP_MS = 150000
tool = lambda s: "anewdsc" if s.startswith("anewdsc") else s

by = collections.defaultdict(list)
for r in csv.DictReader(open(CSV)):
    by[r["case"]].append(r)
_spec = importlib.util.spec_from_file_location("et", os.path.expanduser("~/Desktop/Thesis/notes/tools/eval_tables.py"))
et = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(et)
scored = et.rescore([dict(x) for x in et.load_capped2("and")], CAP_MS)
credited_cells = {(x["case"], x["solver"]) for x in scored if et.cell_ok(x) and float(x["ms"]) <= CAP_MS}
cat_n = collections.Counter()
credited = collections.defaultdict(collections.Counter)
with open(OUT, "w") as fo:
    fo.write("case\tdegree\tcategory\tscoring_count\tcounts_by_arm\tcredited_within_150s\n")
    for case in sorted(by):
        rs = by[case]
        counts = {r["solver"]: int(r["roots"]) for r in rs if r["status"] == "OK"}
        o = int(rs[0]["oracle"])
        if len(set(counts.values())) > 1 or (o >= 0 and any(v != o for v in counts.values())):
            cat = "settled"
        elif len({tool(s) for s in counts}) >= 2:
            cat = "agree"
        elif counts:
            cat = "one-tool"
        else:
            cat = "none"
        cat_n[cat] += 1
        cred = [s for (c, s) in credited_cells if c == case]
        for s in cred:
            credited[s][cat] += 1
        fo.write(f"{case}\t{rs[0]['degree']}\t{cat}\t{o}\t"
                 f"{','.join(f'{k}={v}' for k, v in sorted(counts.items()))}\t{','.join(sorted(cred))}\n")
print("cases by category:", dict(cat_n))
for s in sorted(credited):
    print(f"  {s:12s} credited within 150 s: {sum(credited[s].values()):4d}  by category {dict(credited[s])}")
print("wrote", OUT)

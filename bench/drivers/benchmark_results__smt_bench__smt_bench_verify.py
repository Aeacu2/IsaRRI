#!/usr/bin/env python3
"""Verify the SMT-BENCH phase-2 run2 artifact (docs/SMT_BENCH.md, run2 = THE run).
Read-only; prints PASS/FAIL per check; rc 0 iff all pass. Run from this directory:
    python3 smt_bench_verify.py --tsv results/phase2_run2.tsv --polys results/phase2_run2_polys.tsv

Structural checks (each recomputes from the TSV, never from the doc):
  1  row count = 326 instances x 15 arms x reps (from the header), instances/arms/dup-keys
  7  per-poly sidecar consistency: every OK cell's P-rows sum exactly to its summary row;
     exactly 18 restored-from-log rows asserted (err=restored-from-run2b-log, polys=1)
  8  §3.1 table (doc §3.1): recomputes rank, done@1s, and PAR2-1 for all 15 arms from the
     TSV alone (per-instance: min-of-N cell ms; pari = corrected cells; non-OK cells
     charged 2 s at cap 1 s)

Doc-driven checks 2-6 (run for any tsv; run2 = THE run, run1 = forensics):
  2  §4.1 heaviest-instance table: every cell + the oracle count re-derives from the TSV
  3  §4.1 lost-polys table: anewdsc TO/MIS polys by family re-derived from manifest ndistinct
  4  §1.6 composition table vs manifest
  5  the run1-era PAR2 constants must not be back in the doc
  6  metric-choice sensitivity recomputed and PRINTED as a note (doc makes no claim)

TSV columns: instance arm rep status roots ms polys wall_ms rc err
Pari cells are corrected: min-of-5 wall_ms - PARI_STARTUP_MS, clamped >= 0 (doc §1.5).
"""
import sys, re, argparse
from collections import defaultdict

_ap = argparse.ArgumentParser()
_ap.add_argument('--tsv', default='results/phase2_run2.tsv')
_ap.add_argument('--polys', default='results/phase2_run2_polys.tsv')
_aa = _ap.parse_args()
TSV = _aa.tsv
POLY_TSV = _aa.polys or None
DOC = '../../docs/SMT_BENCH.md'
MANIFEST = 'extracted/manifest.tsv'
# Pari corrected cell = min-of-5 wall_ms - startup, clamped >= 0 (doc §1.5).
# The startup constant is artifact-specific: 12.3 ms measured across the run2 artifact
# (doc quotes 12.3); the run1-era expectations below were computed with 11.9 on run1's
# own min wall, so keep 11.9 when checking the retired run1 TSV.
PARI_STARTUP_MS = 11.9 if 'phase2_run1' in _aa.tsv else 12.3

fails = 0
def chk(cond, msg):
    global fails
    print(('PASS ' if cond else 'FAIL ') + msg)
    if not cond:
        fails += 1

# ---------- load tsv ----------
reps_n = 3
for _h in open(TSV):
    _m = re.match(r'# cap_s=\d+ reps=(\d+)', _h)
    if _m:
        reps_n = int(_m.group(1))
        break
rows = []
with open(TSV) as f:
    for line in f:
        if line.startswith('#') or not line.strip():
            continue
        p = line.rstrip('\n').split('\t')
        rows.append(p)
print(f'rows: {len(rows)}')
exp_rows = 326 * 15 * reps_n
chk(len(rows) == exp_rows, f'row count {exp_rows} (got {len(rows)})')
insts = sorted({r[0] for r in rows})
arms = sorted({r[1] for r in rows})
# oracle per instance = z3 arm's summed roots (z3 is the oracle arm)
oracle = {}
for r in rows:
    if r[1] == 'z3' and r[3] == 'OK':
        oracle[r[0]] = int(r[4])
assert len(oracle) == len(insts), (len(oracle), len(insts))
chk(len(insts) == 326, f'326 instances (got {len(insts)})')
chk(len(arms) == 15, f'15 arms (got {len(arms)})')
chk(len({(r[0], r[1], r[2]) for r in rows}) == len(rows), 'no duplicate (instance, arm, rep) keys')

def cell(inst, arm):
    """min-of-N ms (OK rows); for pari, min-of-N wall_ms - startup."""
    rowsi = [r for r in rows if r[0] == inst and r[1] == arm]
    assert len(rowsi) == reps_n, (inst, arm, len(rowsi))
    if arm == 'pari':
        ws = [float(r[7]) for r in rowsi if r[7] != 'NA']
        assert ws, (inst, arm, rowsi)
        return max(0.0, min(ws) - PARI_STARTUP_MS)
    ms_vals = [float(r[5]) for r in rowsi if r[3] == 'OK' and r[5] != 'NA']
    assert ms_vals, (inst, arm, [r[3:8] for r in rowsi])
    return min(ms_vals)

def classify(inst, arm):
    """OK if all N reps OK and all counts equal the oracle; TO if all TIMEOUT;
    MIS otherwise (mix of statuses or wrong counts)."""
    st = sorted(r[3] for r in rows if r[0] == inst and r[1] == arm)
    counts = {int(r[4]) for r in rows if r[0] == inst and r[1] == arm and r[4] != 'NA'}
    if st == ['OK'] * reps_n:
        return 'OK' if counts == {oracle[inst]} else 'MIS'
    if st == ['TIMEOUT'] * reps_n:
        return 'TO'
    return 'MIS'  # mixed statuses: treat as non-completion

def parse_doc_num(m):
    return float(m.group(1)) * (1000 if m.group(2) else 1)

# ---------- check 7 (new-run per-poly consistency; run1 has no sidecar) ----------
RESTORED = 'restored-from-run2b-log'
if POLY_TSV:
    prs = []
    with open(POLY_TSV) as f:
        for line in f:
            if line.startswith('#') or not line.strip():
                continue
            p = line.rstrip('\n').split('\t')
            prs.append(p)
    keys = [(p[0], p[1], p[2], p[3]) for p in prs]
    chk(len(set(keys)) == len(keys), f'poly rows: no duplicate (instance, arm, rep, poly) keys (got {len(keys)})')
    restored_rows = [r for r in rows if len(r) > 9 and r[9] == RESTORED]
    chk(len(restored_rows) == 18, f'exactly 18 restored-from-log rows (got {len(restored_rows)})')
    chk(all(r[3] == 'OK' and r[5] != 'NA' and r[4] != 'NA' and r[6] == '1' for r in restored_rows),
        'restored rows: status OK, roots/ms present, polys=1 (per-poly row reconstructed: deg from '
        'frozen extracted/<inst>.apolys, roots/ms from the runner log)')
    ok_rows = [r for r in rows if r[3] == 'OK']
    exp_ps = sum(int(r[6]) for r in ok_rows if r[6] != 'NA')
    chk(len(prs) == exp_ps, f'poly rows {len(prs)} == sum of OK polys {exp_ps}')
    bycell = defaultdict(list)
    for p in prs:
        bycell[(p[0], p[1], p[2])].append((int(p[3]), p[5], float(p[6])))
    bad = 0
    for r in ok_rows:
        key = (r[0], r[1], r[2])
        want = int(r[6])
        got = bycell.get(key, [])
        if len(got) != want:
            print(f'  poly-count mismatch {key}: instance says {want}, sidecar has {len(got)}')
            bad += 1
            continue
        psum_r = sum(int(p[1]) for p in got)
        psum_m = sum(p[2] for p in got)
        if psum_r != int(r[4]) or abs(psum_m - float(r[5])) > max(1e-6, 1e-3 * abs(float(r[5]))):
            print(f'  poly-sum mismatch {key}: ({psum_r},{psum_m:.6f}) vs instance ({r[4]},{r[5]})')
            bad += 1
            continue
        if [p[0] for p in got] != list(range(1, want + 1)):
            print(f'  poly idx not 1..N {key}: {[p[0] for p in got]}')
            bad += 1
    chk(bad == 0, f'per-poly consistency: {bad} mismatched cells across {len(ok_rows)} OK rows')
else:
    chk(True, 'no --polys given: per-poly sidecar check skipped')

# ---------- check 8: §3.1 table, per-instance (doc §3.1; 326 instances, cap 1 s) ----------
doc = open(DOC).read()
def par2(arm, cap):
    """PAR2-C in ms: charge every non-completion (TO, MIS) and every cell slower than
    cap seconds at 2*cap seconds (2*cap*1000 ms); OK-fast cells at their true ms."""
    cap_ms = cap * 1000
    tot = 0.0
    for inst in insts:
        if classify(inst, arm) != 'OK':
            tot += 2 * cap_ms
            continue
        v = cell(inst, arm)
        tot += (2 * cap_ms if v > cap_ms else v)
    return tot / len(insts)

def done_at(arm, cap):
    d = mis = to = slow = 0
    for inst in insts:
        c = classify(inst, arm)
        if c == 'OK':
            v = cell(inst, arm)
            if v > cap * 1000: slow += 1
            d += 1
        elif c == 'TO':
            to += 1
        else:
            mis += 1
    return d, mis, to, slow

sec = doc.split('### 3.1')[1].split('Reading the family')[0]
docrows = [l for l in sec.splitlines() if re.match(r'\| \d+ \|', l)]
rank = sorted((par2(a, 1), a) for a in arms)
ok8 = True
for (p, arm), drow in zip(rank, docrows):
    bits = [b.strip() for b in drow.split('|')]
    doc_rank, doc_arm, doc_done, doc_val = int(bits[1]), bits[2], bits[3], bits[4]
    d, mis, to, slow = done_at(arm, 1)
    parts = []
    if mis: parts.append(f'{mis} MIS')
    if to: parts.append(f'{to} TO')
    if slow: parts.append(f'{slow} >cap')
    exp_done = str(d) + (f" (+{', '.join(parts)})" if parts else '')
    exp_val = f'{p:,.3f}'
    exp_rank = rank.index((p, arm)) + 1
    if (doc_arm != arm and not doc_arm.startswith(arm + ' ')) or doc_rank != exp_rank or doc_val != exp_val or doc_done != exp_done:
        chk(False, f'§3.1 row {arm}: doc (r{doc_rank},{doc_done},{doc_val}) '
                   f'vs exp (r{exp_rank},{exp_done},{exp_val})')
        ok8 = False
if ok8:
    chk(True, '§3.1: all 15 rows match (PAR2-1, done@1s, ranks)')

# ---------- doc-driven checks: run for any tsv (run2 = THE run; run1 = forensics) ----------
doc = open(DOC).read()

# ---------- check 1: stale artifacts ----------
chk('[0,1)' not in doc, 'no [0,1) pari cells remain')
chk('its cells are the honest range' not in doc and 'Pari cells are the explicit range' not in doc, 'no [M, M+1) convention remains for SMT cells')
chk('pari is sub-ms' not in doc, 'no "pari is sub-ms" claim remains')
chk('re-ranks pari from 1st' in doc, 'status block pari re-rank present')

# ---------- check 2: §4.1 heaviest-instance table (live; run for any tsv) ----------
# Rows: "| modInvVar1 (71,013) | 81.5 | 36.6 | 19.8 | 16,526.9 | 209.7 | 695.6 | 71.3 |"
# 1st cell = z3's summed oracle; 7 cells = min-of-N reps ms for the 7 shown arms.
HEAVY_ARMS = ['adaptive', 'msolve', 'z3', 'sage', 'cgal', 'libpoly', 'bisection']
HEAVY_INST = {
    'modInvVar1': 'QF_NIA_20230328-sqrtmodinv-hoenicke__modInvVar1.smt2',
    'modInv8': 'QF_NIA_20230328-sqrtmodinv-hoenicke__modInv8.smt2',
    'modInvStep': 'QF_NIA_20230328-sqrtmodinv-hoenicke__modInvStep.smt2',
    'sqrtStepFinala': 'QF_NIA_20230328-sqrtmodinv-hoenicke__sqrtStepFinala.smt2',
    'STC_0563': 'QF_NIA_20220315-MathProblems__STC_0563.smt2',
    'STC_0157': 'QF_NIA_20220315-MathProblems__STC_0157.smt2',
}
sec41 = doc.split('### 4.1')[1].split('## 5.')[0]
docrows41 = [l for l in sec41.splitlines()
             if re.match(r'\| [A-Za-z0-9_]+ \(\d[\d,]*\) \|', l)]
ok_heavy = True
for drow in docrows41:
    bits = [b.strip() for b in drow.split('|')]
    short = bits[1].split(' ')[0]
    if short not in HEAVY_INST:
        continue
    inst = HEAVY_INST[short]
    doc_oracle = int(bits[1].split('(')[1].split(')')[0].replace(',', ''))
    doc_cells = {a: float(b.replace(',', '')) for a, b in zip(HEAVY_ARMS, bits[2:2 + len(HEAVY_ARMS)])}
    exp_oracle = oracle[inst]
    if doc_oracle != exp_oracle:
        chk(False, f'§4.1 {short}: oracle doc {doc_oracle} vs tsv {exp_oracle}')
        ok_heavy = False
    for a, exp_val in [(a, cell(inst, a)) for a in HEAVY_ARMS]:
        if abs(doc_cells[a] - exp_val) > 0.06:
            chk(False, f'§4.1 {short}/{a}: doc {doc_cells[a]} vs exp {exp_val:.4f}')
            ok_heavy = False
if ok_heavy:
    chk(True, f'§4.1 heaviest table: {len(docrows41)} rows, all cells + oracles match')

# ---------- check 3: §4.1 lost-polys table (by family, TO/MIS split) ----------
fam_nd = {}
with open(MANIFEST) as f:
    for _l in f:
        _p = _l.rstrip('\n').split('\t')
        if len(_p) >= 4 and _p[0] != 'instance':
            fam_nd[_p[0]] = (_p[1], int(_p[3]))
to_by_fam = defaultdict(int)
mis_by_fam = defaultdict(int)
for i in insts:
    st = sorted(r[3] for r in rows if r[0] == i and r[1] == 'anewdsc')
    fam, nd = fam_nd.get(i, ('?', 0))
    if st == ['TIMEOUT'] * 5:
        to_by_fam[fam] += nd
    else:
        counts = {int(r[4]) for r in rows if r[0] == i and r[1] == 'anewdsc' and r[4] != 'NA'}
        if counts != {oracle[i]} or st != ['OK'] * 5:
            mis_by_fam[fam] += nd
ok_lost = True
FAM_SHORT = {  # doc's §4.1 short family names -> manifest family strings
    'MathProblems': 'QF_NIA/20220315-MathProblems',
    'sqrtmodinv-hoenicke': 'QF_NIA/20230328-sqrtmodinv-hoenicke',
    'VeryMax': 'QF_NIA/20170427-VeryMax',
    'hycomp': 'QF_NRA/hycomp',
    'LassoRanker': 'QF_NRA/LassoRanker',
    'UltimateAutomizerSvcomp2023': 'QF_NIA/20230321-UltimateAutomizerSvcomp2023',
    'Heizmann': 'QF_NRA/20170501-Heizmann-UltimateInvariantSynthesis',
    'AProVE': 'QF_NIA/AProVE',
}
lost_rows = [l for l in sec41.splitlines()
             if re.match(r'\| [^|]+ \| ([\d,]+|—) \| ([\d,]+|—) \|$', l)]
for line in lost_rows:
    bits = [b.strip() for b in line.split('|')]
    if len(bits) < 3 or not bits[1]:
        continue
    fam, to_, mis_ = bits[1], bits[2], bits[3]
    fam = FAM_SHORT.get(fam, fam)
    exp_to = to_by_fam.get(fam, 0)
    exp_mis = mis_by_fam.get(fam, 0)
    d_to = int(to_.replace(',', '')) if to_ != '—' and to_ != '- ' else 0
    d_mis = int(mis_.replace(',', '')) if mis_ not in ('—', '') else 0
    if (d_to, d_mis) != (exp_to, exp_mis):
        chk(False, f'§4.1 lost-polys {fam}: doc ({d_to},{d_mis}) vs exp ({exp_to},{exp_mis})')
        ok_lost = False
if ok_lost:
    chk(True, f'§4.1 lost-polys table: {len(lost_rows)} rows match (total {sum(to_by_fam.values()) + sum(mis_by_fam.values())})')

# ---------- check 4: composition table (§1.6) ----------
comp = defaultdict(lambda: [0, 0])
with open(MANIFEST) as f:
    next(f)
    for line in f:
        p = line.rstrip('\n').split('\t')
        comp[p[1]][0] += 1
        comp[p[1]][1] += int(p[3])
sec16 = doc.split('### 1.6')[1].split('## 2.')[0]
tbl16 = [l for l in sec16.splitlines() if l.startswith('| ') and 'corpus' not in l]
chk(len(tbl16) == len(comp), f'composition table rows: {len(tbl16)} vs manifest {len(comp)}')
mism = 0
for line in tbl16:
    bits = [b.strip() for b in line.split('|')]
    c, ni, np_ = bits[1], int(bits[2].replace(',', '')), int(bits[3].replace(',', ''))
    if comp[c] != [ni, np_]:
        print(f'  composition mismatch {c}: doc ({ni},{np_}) vs manifest {comp[c]}')
        mism += 1
chk(mism == 0, f'composition cells: {mism} mismatches')
tot = sum(v[1] for v in comp.values())
sortedf = sorted(comp, key=lambda k: -comp[k][1])
top3 = sum(comp[k][1] for k in sortedf[:3])
top4 = sum(comp[k][1] for k in sortedf[:4])
chk(tot == 341282, f'total polys 341,282 (got {tot})')
chk(f'{top3/tot:.3f}' == '0.897', f'top-3 share 89.7% (got {top3/tot:.3f})')
chk(f'{top4/tot:.3f}' == '0.929', f'top-4 share 92.9% (got {top4/tot:.3f})')

# ---------- check 5: stale run1-era constants must not be in the doc ----------
for stale in ['8.933', '13,893', '294.821', '204.455', '514.719']:
    chk(stale not in doc, f'no run1-era constant {stale!r} remains in the doc')

# ---------- check 6: metric-choice sensitivity (ms vs wall-based PAR2-150) ----------
wall_cell = {}
for a in arms:
    for i in insts:
        ws = [float(r[7]) for r in rows if r[0] == i and r[1] == a and r[7] != 'NA']
        wall_cell[(i, a)] = min(ws) if ws else None
startup = {a: min(w for w in (wall_cell[(i, a)] for i in insts) if w is not None) for a in arms}
def par2_wall(a, cap):
    cap_ms = cap * 1000
    tot = 0.0
    for i in insts:
        if classify(i, a) != 'OK':
            tot += 2 * cap_ms
            continue
        v = max(0.0, wall_cell[(i, a)] - startup[a])
        tot += (2 * cap_ms if v > cap_ms else v)
    return tot / len(insts)
ranks_ms = sorted(arms, key=lambda a: par2(a, 150))
ranks_w = sorted(arms, key=lambda a: par2_wall(a, 150))
swaps = [(ranks_ms.index(a) + 1, a, ranks_w.index(a) + 1) for a in arms if ranks_ms.index(a) != ranks_w.index(a)]
if 'run1' in TSV:
    print('NOTE metric-choice sensitivity (run1 forensics): wall-vs-ms PAR2-150 rank swaps:',
          swaps if swaps else 'none')
else:
    print('NOTE metric-choice sensitivity (run2): wall-vs-ms PAR2-150 rank swaps:',
          swaps if swaps else 'none')
    print('  (doc makes no invariance claim; the 2026-08-08 run1-era "rank-invariant" memory')
    print('   was superseded 2026-08-09 — run2 has the adjacent swaps above; the tables are MS-based)')

print()
print('FAILURES:', fails)
sys.exit(1 if fails else 0)

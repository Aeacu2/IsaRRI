#!/usr/bin/env bash
# thesis-campaign-audit.sh — the post-run contamination audit for the thesis campaign.
#
# WHY IT IS ITS OWN SCRIPT, AND WHY IT SELF-TESTS.  The audit that used to live inline at the end
# of thesis-campaign-run.sh could not fire: it parsed `*_results.csv` — a real comma-separated CSV
# written by csv.writer — with `awk -F'\t'`, so the whole line landed in $1 and the two guards read
# `$10`/`$11` as empty. The sleep guard's test `$10+0 > 160000` was then `0 > 160000`, FALSE on
# every row forever; the non-OK guard's `$11!="OK"` was TRUE on every row, so it printed the entire
# file and a real failure was indistinguishable from the noise. Both guards were inverted by one
# character. A guard that cannot fail is worse than no guard, so this one PROVES itself on
# synthetic rows before it is trusted (`--selftest`, run automatically first).
#
# THE FOUR CHECKS
#   1. SLEEP — a rep recorded OK whose own duration exceeds the cap. On macOS a system sleep freezes
#      the process AND the monotonic clock, so `timeout=` never fires and the row reads as a slow
#      machine, not as breakage (`sleep-inflation-contaminates-reps`). ⚠️ This must be read off the
#      PER-REP log lines, not the CSV: the CSV's `ms` is the MIN over completed reps, so a single
#      inflated rep is hidden by the min — the very case the rule exists for.
#   2. NON-OK — every ERROR/PARSE_ERROR cell, counted per solver. ERROR rows are OURS until traced
#      (`ERROR` rows have three times been our bug, not the competitor's).
#   3. ORACLE (gate T-f) — root counts against the table's own oracle column, per solver. The
#      campaign runner had no automated step for this at all.
#   4. FLOOR — the cross-binary link-layout floor, measured rather than assumed: powsub_l4 and
#      powsub_ship are two BINARIES, so their ratio carries a layout component. On cases where L4
#      provably never fires the ratio IS the floor, which is what gates T-c/T-d (bars 0.98) need in
#      order to mean anything.
#
#   1b. SLEEP, CAMPAIGN 2 — from 2026-09-19 an over-cap rep is reclassified TIMEOUT by the driver
#      ("over cap on solve time (N ms) -> TIMEOUT"), so a sleep no longer leaves an OK row. Kill is at
#      cap + 15 s wall; a reclassified rep whose solve time exceeds that means the clock stopped.
#      Per-leg run cap: MPSolve 60 s, AND 180 s (AND case names start with "and").
#   6. REP SPREAD, CAMPAIGN 2 — the early-stop rules assume a later rep cannot beat the first by the
#      headroom between run cap and scoring cap (AND 180/150 s: 16.7%; MPSolve has no early stop). That was
#      measured under campaign 1's scheduling (back-to-back reps). Campaign 2 rotates arms per rep, so
#      re-measure it here: over cells with >= 2 completed reps of >= 1 s, p95 of (max/min - 1) must be
#      <= 5%, and every cell above 16.7% is listed.
#   5. GUARD — cases the non-blocking guard measured while foreign CPU was busy (*.guard.tsv).
#      Every listed case must be re-measured (delete its rows, resume) before scoring.
#
# USAGE  thesis-campaign-audit.sh [<campaign-out-dir>]    |    thesis-campaign-audit.sh --selftest
set -uo pipefail
cd "$(dirname "$0")/.."
REPO="$PWD"
CAP_MS="${CAP_MS:-150000}"
SLEEP_MS="${SLEEP_MS:-160000}"   # cap + ~7%: above this an OK rep means the clock stopped

# ---- the two row predicates, as functions so the selftest can exercise them ----------------
sleep_suspects() {  # <per-rep log...>: prints rep lines recorded OK above SLEEP_MS
  grep -hE 'rep[0-9]+ OK ' "$@" 2>/dev/null \
    | sed -E 's/.* ([0-9.]+)ms$/\1 &/' \
    | awk -v lim="$SLEEP_MS" '$1+0 > lim {$1=""; print "    SLEEP-SUSPECT:"$0}'
}
sleep_suspects_c2() {  # <log...>: reclassified over-cap reps beyond cap + 15 s kill slack
  grep -hE 'over cap on solve time \([0-9]+ ms\)' "$@" 2>/dev/null \
    | awk '{ match($0, /\(([0-9]+) ms\)/); ms = substr($0, RSTART + 1, RLENGTH - 5) + 0
             split($1, a, "/"); lim = (a[1] ~ /^and/) ? 195000 : 75000
             if (ms > lim) print "    SLEEP-SUSPECT(c2):", $0 }'
}
guard_rows() {        # <guard.tsv...>: foreign CPU seen at a non-blocking check, orphan reaps
  cat "$@" 2>/dev/null | awk -F'\t' 'NF >= 2 {print "    GUARD:", $2, "--", substr($3, 1, 100)}'
}
rep_spread() {       # <log...>: per-cell spread of completed reps (>= 1 s), in log order
  python3 - "$@" <<'PY'
import re, sys, collections
reps = collections.defaultdict(list)
for p in sys.argv[1:]:
    try: fh = open(p, errors="replace")
    except OSError: continue
    for line in fh:
        m = re.match(r"\s+(\S+)/(\S+) rep\d+ OK roots=-?\d+ ([\d.]+)ms", line)
        if m: reps[(m.group(1), m.group(2))].append(float(m.group(3)))
sp = sorted((max(v) / min(v) - 1, k) for k, v in reps.items() if len(v) >= 2 and min(v) >= 1000)
if not sp: print("    no cell with >= 2 completed reps of >= 1 s"); sys.exit(0)
p95 = sp[max(0, -(-95 * len(sp) // 100) - 1)][0]   # nearest-rank: ceil(0.95 n) - 1
print(f"    cells {len(sp)}  median {100 * sp[len(sp) // 2][0]:.2f}%  p95 {100 * p95:.2f}%  max {100 * sp[-1][0]:.2f}%")
for v, k in sp:
    if v > 0.167: print(f"    SPREAD-ABOVE-HEADROOM: {k[0]}/{k[1]} {100 * v:.1f}%")
print("    bar p95 <= 5%: " + ("PASS" if p95 <= 0.05 else "FAIL -- the early-stop headroom argument does not hold"))
PY
}
nonok_rows() {      # <results.csv...>: prints non-OK rows (field 11 of a REAL csv)
  python3 - "$@" <<'PY'
import csv, sys
for p in sys.argv[1:]:
    try: fh = open(p, newline="")
    except OSError: continue
    for r in csv.DictReader(fh):
        if r.get("status") and r["status"] != "OK":
            print(f"    NON-OK: {p.split('/')[-1]} {r['case']} {r['solver']} {r['status'][:60]}")
PY
}

if [ "${1:-}" = "--selftest" ] || [ "${SELFTEST:-0}" = "1" ]; then
  T=$(mktemp -d)
  printf 'case,id,band,family,degree,params,oracle,solver,roots,ms,status\n' > "$T/r.csv"
  printf 'c1,1,1,f,8,p,2,powsub_l4,2,12.5,OK\n' >> "$T/r.csv"
  printf 'c2,2,1,f,8,p,2,sage,-1,-1,ERROR:boom\n' >> "$T/r.csv"
  printf '    c1/powsub_l4 rep1 OK roots=2 12.500ms\n'      > "$T/l.log"
  printf '    c2/sage rep1 OK roots=2 999999.000ms\n'      >> "$T/l.log"
  printf '    lsr3/cgal rep1 over cap on solve time (70000 ms) -> TIMEOUT\n'  > "$T/c2.log"
  printf '    lsr3/cgal rep2 over cap on solve time (900000 ms) -> TIMEOUT\n' >> "$T/c2.log"
  printf '    and05_x/sage rep1 over cap on solve time (190000 ms) -> TIMEOUT\n' >> "$T/c2.log"
  printf '2026-09-19T00:00:00\tcase and05_x\tpid=1 cpu=90 foo\n' > "$T/g.tsv"
  printf '    cA/sage rep1 OK roots=2 1000.0ms\n    cA/sage rep1 OK roots=2 1300.0ms\n' > "$T/sp.log"
  printf '    cB/cgal rep1 OK roots=2 2000.0ms\n    cB/cgal rep1 OK roots=2 2010.0ms\n' >> "$T/sp.log"
  ns=$(sleep_suspects "$T/l.log" | wc -l | tr -d ' ')
  nn=$(nonok_rows "$T/r.csv" | wc -l | tr -d ' ')
  n2=$(sleep_suspects_c2 "$T/c2.log" | wc -l | tr -d ' ')
  ng=$(guard_rows "$T/g.tsv" | wc -l | tr -d ' ')
  nsp=$(rep_spread "$T/sp.log" | grep -c 'SPREAD-ABOVE-HEADROOM: cA/sage')
  nfail=$(rep_spread "$T/sp.log" | grep -c 'FAIL')
  rm -rf "$T"
  [ "$n2" = "1" ] || { echo "SELFTEST FAIL: c2 sleep guard found $n2/1" >&2; exit 1; }
  [ "$ng" = "1" ] || { echo "SELFTEST FAIL: guard-log reader found $ng/1" >&2; exit 1; }
  [ "$nsp" = "1" ] || { echo "SELFTEST FAIL: rep-spread did not flag the planted 30% cell" >&2; exit 1; }
  [ "$nfail" = "1" ] || { echo "SELFTEST FAIL: rep-spread bar did not fail on a planted p95 of 30%" >&2; exit 1; }
  [ "$ns" = "1" ] || { echo "SELFTEST FAIL: sleep guard found $ns/1" >&2; exit 1; }
  [ "$nn" = "1" ] || { echo "SELFTEST FAIL: non-OK guard found $nn/1" >&2; exit 1; }
  echo "audit selftest: all five guards fire on a planted row and only on it — OK"
  [ "${1:-}" = "--selftest" ] && exit 0
fi

OUT="${1:-$REPO/benchmark_results/data/thesis_campaign_2026-09-12}"
CSVS=("$OUT"/mpsolve_results.csv "$OUT"/and_results.csv)
LOGS=("$OUT"/campaign.log "$OUT"/pipeline.log)

echo "== campaign audit  $(date -u +%FT%TZ)   out=$OUT"
SELFTEST=1 "$0" --selftest || exit 1

echo "-- 1. SLEEP (a rep recorded OK above ${SLEEP_MS}ms; MUST be empty)"
s=$(sleep_suspects "${LOGS[@]}"); if [ -n "$s" ]; then echo "$s"
  echo "    🔴 the machine slept: those ROWS are void — discard, do not drop the outlier"
else echo "    none"; fi

echo "-- 1b. SLEEP, campaign 2 (over-cap reclassified rep beyond cap + 15 s; MUST be empty)"
s=$(sleep_suspects_c2 "${LOGS[@]}"); if [ -n "$s" ]; then echo "$s"
  echo "    🔴 the clock stopped during those reps: re-measure those cases"
else echo "    none"; fi

echo "-- 2. NON-OK cells, per solver"
n=$(nonok_rows "${CSVS[@]}")
if [ -n "$n" ]; then echo "$n" | head -40
  echo "$n" | awk '{print $4}' | sort | uniq -c | sort -rn | sed 's/^/    count /'
  echo "    ⚠️ ERROR rows are OURS until traced (pari stack, z3 gcd, python int limit)"
else echo "    none"; fi

echo "-- 3. ORACLE (gate T-f): root count vs the table's oracle column"
python3 - "${CSVS[@]}" <<'PY'
import csv, sys, collections
bad = collections.Counter(); seen = collections.Counter(); rows = []
for p in sys.argv[1:]:
    try: fh = open(p, newline="")
    except OSError: continue
    for r in csv.DictReader(fh):
        if r.get("status") != "OK": continue
        try: orc, got = int(r["oracle"]), int(r["roots"])
        except (TypeError, ValueError): continue
        if orc < 0: continue                      # suite's "no oracle" convention
        seen[r["solver"]] += 1
        if orc != got:
            bad[r["solver"]] += 1
            rows.append(f"    MISCOUNT: {r['case']} {r['solver']} got={got} oracle={orc}")
for x in rows[:40]: print(x)
if not rows: print("    none — every OK cell with an oracle matches")
for s in sorted(seen): print(f"    checked {seen[s]:5d}  miscount {bad[s]:4d}  {s}")
print("    ⚠️ a disagreement is adjudicated by polsturm, not by majority vote")
PY

echo "-- 4. FLOOR: powsub_l4 vs powsub_ship (two BINARIES — the ratio carries link layout)"
python3 - "${CSVS[@]}" <<'PY'
import csv, sys, statistics as st
for p in sys.argv[1:]:
    a = {}
    try: fh = open(p, newline="")
    except OSError: continue
    for r in csv.DictReader(fh):
        if r.get("status") == "OK" and r["solver"] in ("powsub_l4", "powsub_ship"):
            a.setdefault(r["case"], {})[r["solver"]] = float(r["ms"])
    rs = [v["powsub_ship"] / v["powsub_l4"] for v in a.values()
          if len(v) == 2 and v["powsub_l4"] > 0]
    if not rs:
        print(f"    {p.split('/')[-1]}: N/A -- no powsub_ship rows (campaign 2 has one IsaRRI arm)")
        continue
    near = [x for x in rs if 0.97 <= x <= 1.03]
    print(f"    {p.split('/')[-1]}: {len(rs)} paired rows  geomean {st.geometric_mean(rs):.4f} "
          f"min {min(rs):.3f} max {max(rs):.3f}")
    if near:
        print(f"      inert-ish band (0.97-1.03): {len(near)} rows, spread "
              f"{max(near)-min(near):.4f}  <- read the FLOOR off these")
    print("      🔴 T-c/T-d bars are 0.98; if the floor spread approaches 2% those gates "
          "cannot resolve their own bar")
PY
echo "-- 6. REP SPREAD, campaign 2 (the early-stop headroom assumption, re-measured on this run)"
rep_spread "${LOGS[@]}"

echo "-- 5. GUARD: cases measured while foreign CPU was busy (re-measure each before scoring)"
G=$(guard_rows "$OUT"/*.guard.tsv "$REPO"/benchmark_results/smt_bench/results/campaign2_run1.tsv.guard.tsv)
if [ -n "$G" ]; then echo "$G" | head -60; echo "    $(echo "$G" | wc -l | tr -d ' ') entries"
else echo "    none"; fi
echo "== audit done"

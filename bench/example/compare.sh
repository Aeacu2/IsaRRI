#!/usr/bin/env bash
# One complete comparison from the public supplement alone: IsaRRI (public export) against PARI
# (its realroots with the squarefree step removed, bench/drivers/*pari_realroots_nosqf.c) on one
# MPSolve-Bench input, with the campaign's protocol in miniature:
#   input digest checked against the manifest; 3 repetitions, each running both arms once in an
#   order that alternates; each arm timed around its isolation call only; recorded time = minimum;
#   both counts checked against a Sturm-sequence count (bench/sturm); scored as MPSolve-Bench scores
#   a case (60 s cap: correct and within the cap -> its time, otherwise 120 s).
# Needs clang, GMP, PARI/GP 2.17 with its library (e.g. Homebrew's pari). Usage:
#   bench/example/compare.sh [input file] [GMP prefix] [PARI prefix]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"; BENCH="$(dirname "$HERE")"; ROOT="$(dirname "$BENCH")"
IN="${1:-$HERE/chebyshev320.txt}"
GMP="${2:-$(brew --prefix gmp 2>/dev/null || echo /opt/homebrew)}"
PARI="${3:-$(brew --prefix pari 2>/dev/null || echo /opt/homebrew)}"
B="$(mktemp -d)"
make -s -C "$HERE" GMP="$GMP" time_one
clang -O2 -w -I"$PARI/include" "$BENCH/drivers/Dsc__export__c_harness__pari_timer.c" \
  "$BENCH/drivers/Dsc__export__c_harness__pari_realroots_nosqf.c" -L"$PARI/lib" -lpari -o "$B/pari_timer" \
  2>/dev/null || clang -O2 -w -I"$PARI/include" "$BENCH/drivers/Dsc__export__c_harness__pari_timer.c" \
  "$BENCH/drivers/Dsc__export__c_harness__pari_realroots_nosqf.c" -L"$PARI/lib" -lpari-gmp-tls -o "$B/pari_timer"
name="$(basename "$IN" .txt)"
want=$(awk -F'\t' -v n="/$name.txt" 'index($2, n) {print $4}' "$BENCH/inputs/MANIFEST.tsv")
have=$(shasum -a 256 "$IN" | cut -d' ' -f1)
if [ -n "$want" ]; then [ "$want" = "$have" ] || { echo "digest mismatch" >&2; exit 1; }; echo "input $name: digest matches the manifest"; fi
ti=(); tp=()
for r in 1 2 3; do
  if [ $((r % 2)) = 1 ]; then order="isarri pari"; else order="pari isarri"; fi
  for arm in $order; do
    if [ $arm = isarri ]; then out=$("$HERE/time_one" "$IN" 1); ri=$(echo "$out" | sed 's/.*roots=\([0-9]*\).*/\1/'); ti+=($(echo "$out" | sed 's/.*ms=\([0-9.]*\).*/\1/'))
    else out=$("$B/pari_timer" --solve-stdin "$name" pari 1 < "$IN"); rp=$(echo "$out" | sed 's/.*pari_roots=\([0-9]*\).*/\1/'); tp+=($(echo "$out" | sed 's/.*pari_ms=\([0-9.e+-]*\).*/\1/')); fi
  done
done
sturm=$(python3 "$BENCH/sturm/check_one.py" "$IN" --gmp "$GMP" | awk -F'\t' '{print $2, $3+$4+$5}')
status=${sturm%% *}; ref=${sturm##* }
[ "$status" = OK ] || { echo "IsaRRI's windows failed the Sturm check: $sturm" >&2; exit 1; }
min() { printf '%s\n' "$@" | sort -g | head -1; }
mi=$(min "${ti[@]}"); mp=$(min "${tp[@]}")
score() { awk -v t="$1" -v ok="$2" 'BEGIN { if (ok && t <= 60000) printf "%.3f", t/1000; else printf "120"; }'; }
echo "Sturm count: $ref (IsaRRI's windows also pass the window check)"
printf "%-8s %6s %10s %8s  %s\n" arm roots min_ms score_s runs_ms
printf "%-8s %6s %10s %8s  %s\n" IsaRRI "$ri" "$mi" "$(score "$mi" $([ "$ri" = "$ref" ] && echo 1 || echo 0))" "${ti[*]}"
printf "%-8s %6s %10s %8s  %s\n" PARI "$rp" "$mp" "$(score "$mp" $([ "$rp" = "$ref" ] && echo 1 || echo 0))" "${tp[*]}"
echo "recorded in the campaign (bench/results/mpsolve.csv):"
grep "^$name," "$BENCH/results/mpsolve.csv" | awk -F, '$8=="IsaRRI" || $8=="pari" {print "  " $8, $9, $10, $11}'
rm -rf "$B"

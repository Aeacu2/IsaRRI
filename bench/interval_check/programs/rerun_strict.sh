#!/bin/bash
# Rerun every competitor interval check under the strict endpoint reading (2026-10-24 review, finding 1):
# a point is discounted only from a window that ends at it. Old results: superseded_2026-10-24_interior_points/.
# Counts, not timings; never beside a measured job.
set -u
cd "$(dirname "$0")"
R=~/Desktop/Dsc_LLVM
python3 $R/scripts/b2/check_risolate_windows.py --selftest || exit 1
python3 check_reduced_windows.py --selftest || exit 1
# the sets the rescoring reads first; AND-Bench, the slowest, last
for w in $(for s in smt heldout mpsolve logcfbench ccluster and; do ls windows_${s}_*.tsv; done); do
  case $w in *.check.tsv) continue;; esac
  s=${w#windows_}; suite=${s%%_*}
  echo "== $(date +%T) $w ($suite)"
  if [[ $w == *_parisqf.tsv ]]; then python3 check_reduced_windows.py "$suite" "$w" --jobs 6
  else case $suite in smt|heldout) sh=400;; *) sh=4;; esac   # large polynomials: small shards, so 6 workers share them
       python3 $R/scripts/b2/check_risolate_windows.py "$suite" "$w" --open --jobs 6 --shard $sh; fi
done
echo "== $(date +%T) done"

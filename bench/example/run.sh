#!/usr/bin/env bash
# One benchmark case end to end against the public export: build, check the input's digest against
# the manifest, time IsaRRI with the campaign's protocol (3 runs, minimum), and print the recorded
# campaign row for comparison. Usage: bench/example/run.sh [GMP prefix]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
BENCH="$(dirname "$HERE")"
GMP="${1:-$(brew --prefix gmp 2>/dev/null || echo /opt/homebrew)}"
make -s -C "$HERE" GMP="$GMP" time_one
IN="$HERE/chebyshev320.txt"
want=$(awk -F'\t' '$2 ~ /chebyshev320.txt$/ {print $4}' "$BENCH/inputs/MANIFEST.tsv")
have=$(shasum -a 256 "$IN" | cut -d' ' -f1)
[ "$want" = "$have" ] || { echo "digest mismatch: $have vs manifest $want" >&2; exit 1; }
echo "input chebyshev320 (MPSolve-Bench): digest matches the manifest"
echo -n "this machine: "; "$HERE/time_one" "$IN" 3
echo "recorded (bench/results/mpsolve.csv, reference count, arm, roots, ms, status):"
grep '^chebyshev320,' "$BENCH/results/mpsolve.csv" | awk -F, '$8=="IsaRRI" || $8=="msolve" {print "  " $7, $8, $9, $10, $11}'

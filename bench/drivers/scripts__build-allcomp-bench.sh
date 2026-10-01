#!/usr/bin/env bash
# build-allcomp-bench.sh — build ONE arm binary for the all-competitors campaign.
#
# NAMING (user, 2026-09-12): the campaign's binaries are `allcomp_bench_<label>`. The name
# "suite_v2" is retired from everything this campaign touches — it named a 2026-07 harness
# revision, carries no meaning here, and its old binaries measure entries that no longer ship.
# ⚠️ The C++ SOURCE is still `suite_v2_bench.cpp`: eight legacy scripts and every archived
# PROVENANCE cite that path, so renaming it is a separate, wider change. Nothing the campaign
# RUNS is called suite_v2.
#
# ⛔ NEVER reuse the old binaries for this campaign:
#   suite_v2_bench_post  Aug 8   suite_v2_bench_e1  Aug 10   suite_v2_bench_pre  (vcap, retired)
# all predate R, E3, L3-wide, D8, track D and the Sep 3 ships.
#
# 🔴 LINKS runtime/lib_isabelle_llvm.c — the .c (L3 freelist). The .cpp is a naive `new char[]()`;
#    linking it once cost 24.8% and masqueraded as probe overhead
#    (docs/memory/link-the-runtime-the-harness-links.md).
#
# 🔴 A new binary name must also be in bench-guard.sh's SOLVER_RE or --strict/--stop cannot see it.
#
# usage: build-allcomp-bench.sh <label> [path/to/artifact.ll]
#   label = l4   -> the post-L4 export   (the thesis arm)
#   label = ship -> f3f96e19, L1+L2m     (the A/B control; see docs/THESIS_CAMPAIGN_PLAN.md §3)
set -euo pipefail
cd "$(dirname "$0")/.."
REPO="$PWD"
HARNESS="$REPO/Dsc/export/c_harness"
BUILD="$HARNESS/build"
GMP="${GMP_PREFIX:-$(brew --prefix gmp 2>/dev/null || echo /opt/homebrew)}"

LABEL="${1:-}"
case "$LABEL" in
  l4|ship) ;;
  *) echo "usage: $0 <l4|ship> [artifact.ll]" >&2; exit 2 ;;
esac
LL="${2:-${DSC_LL:-$REPO/Dsc/export/dsc_adaptive.ll}}"
OUT="$BUILD/allcomp_bench_$LABEL"

[ -f "$LL" ] || { echo "FATAL: no .ll at $LL" >&2; exit 1; }
mkdir -p "$BUILD"

echo "== artifact"
shasum -a 256 "$LL"
echo "   (record this in the run's PROVENANCE — a timing without its artifact sha is unciteable)"

echo "== entries present in the artifact"
for e in all_dsc_adaptive_main all_dsc_powsub_main all_dsc_lowdeg_main all_dsc_bisection_main; do
  grep -q "^define.*@$e(" "$LL" || { echo "FATAL: $e missing from $LL" >&2; exit 1; }
  echo "   ok  $e"
done

echo "== runtime shim (the .c — L3 freelist)"
clang -O2 -w -c "$HARNESS/runtime/lib_isabelle_llvm.c" -o "$BUILD/lib_isabelle_llvm_$LABEL.o"

echo "== harness"
clang++ -std=c++17 -O2 -w -DDSC_ENTRIES_PUBLIC -I"$GMP/include" \
  "$HARNESS/suite_v2_bench.cpp" "$LL" "$BUILD/lib_isabelle_llvm_$LABEL.o" \
  -L"$GMP/lib" -lgmpxx -lgmp -o "$OUT"

echo "== built: $OUT"
ls -la "$OUT"
echo
# 🔴 DO NOT probe this binary with an unknown flag. There is no --help/--list-entries verb and an
# unrecognised argv FALLS THROUGH TO RUNNING THE WHOLE SUITE (that cost a stray full-suite run on
# 2026-09-05). The only safe introspection is --solve-stdin with a deliberately WRONG entry name:
# it prints the compiled-in list to stderr and exits 2.
echo "== arms this binary exposes (via --solve-stdin's error path — the only safe probe)"
echo "1,0,1" | "$OUT" --solve-stdin probe __list__ 1 5 2>&1 | head -2 || true
echo
echo "== functional check: powsub on P = 1 + x^2 (0 real roots)"
echo "1,0,1" | "$OUT" --solve-stdin probe powsub 1 30 2>&1 | head -2
echo "   (expect powsub_roots=0; a nonzero/absent count means the adapter is wrong — STOP)"

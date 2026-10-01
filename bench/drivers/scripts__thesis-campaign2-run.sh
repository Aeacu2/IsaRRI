#!/usr/bin/env bash
# thesis-campaign2-run.sh — the thesis re-benchmark (docs/THESIS_CAMPAIGN2_PLAN.md, 2026-09-18).
#
# WHY A SECOND CAMPAIGN. The 2026-09-12 campaign did not time every arm on the same task:
#   z3 on MPSolve/AND ran isolate_roots (squarefree decomposition + isolation), Sage ran
#   real_root_intervals (squarefree decomposition), PARI ran polrootsreal (squarefree factorisation
#   + refinement to 38 digits, timed by gp in whole ms), and libpoly was timed on roots_count +
#   roots_isolate (two full solves). MPSolve/AND arms were interleaved per case but each arm's reps
#   ran back to back, and the MPSolve leg was not rotated at all.
# This campaign: every arm isolates a squarefree input with no squarefree preprocessing, and on
# every suite each repetition runs every arm once, in an order rotated per (case, repetition).
#
# Three legs, sequential, one measured job at a time; NOTHING else may run beside it
# (no Isabelle build, no latexmk, no other benchmark):
#   1. mpsolve  (131 cases x 9 arms, cap 60 s, 3 reps, no early stop, rep-major)
#   2. smt      (326 instances x 9 arms, cap 1 s classification, 5 reps, rotated per rep)
#   3. and      (295 cases x 9 arms, cap 180 s, 2 reps, rep-major, ladder skip as in campaign 1;
#                headline tables scored at 150 s, docs/THESIS_CAMPAIGN2_PLAN.md §6 item 8)
# Panel (9): powsub_l4 (= IsaRRI), msolve, anewdsc (-S 1), anewdsc_i0 (-S 1 -i 0, sensitivity arm),
#            sagesqf, parisqf, z3sqf (z3 on SMT), cgal, libpolysqf.
# Cap: every arm killed at cap + 15 s wall; a rep completes iff its self-reported solve time <= cap
# (final-suite-run.py KILL_SLACK_S). Early stop: none on MPSolve (all 3 reps); an AND cell is finished
# after its 1st timed-out rep, and AND is RUN at 180 s but SCORED at 150 s, so that the stop has headroom.
# Guard: blocking strict check once per family/corpus; elsewhere non-blocking, logged to *.guard.tsv.
#
# Resume-safe: every leg resumes from its own output (final-suite-run.py done-set; phase2
# --resume), so re-invoking never re-measures a recorded cell. A case interrupted mid-way is
# re-run whole (rep-major writes a case's rows only after all its reps).
#
# USAGE
#   ./scripts/thesis-campaign2-run.sh                 # all three legs
#   ./scripts/thesis-campaign2-run.sh --leg mpsolve|smt|and
set -uo pipefail
cd "$(dirname "$0")/.."
REPO="$PWD"

OUT="$REPO/benchmark_results/data/thesis_campaign2_2026-09-18"
MPS_TABLE="$REPO/benchmark_results/mpsolve_suite/cases_record.json"
MPS_COEFFS="$REPO/benchmark_results/mpsolve_suite/coeffs"
AND_TABLE="$REPO/benchmark_results/and_bench/cases_record.json"
AND_COEFFS="$REPO/benchmark_results/and_bench/coeffs"
DRIVER="$REPO/scripts/final-suite-run.py"
SMT_DRIVER="$REPO/benchmark_results/smt_bench/smt_bench_phase2.py"
GUARD="$REPO/scripts/bench-guard.sh"
L4_LL="$REPO/Dsc/export/dsc_adaptive.ll"
LOG="$OUT/campaign.log"
PROV="$OUT/PROVENANCE.txt"
H="$REPO/Dsc/export/c_harness"

LEG="all"
while [[ $# -gt 0 ]]; do
  case "$1" in
    --leg) LEG="$2"; shift 2;;
    -h|--help) sed -n '2,20p' "$0" | sed 's/^# //; s/^#//'; exit 0;;
    *) echo "unknown arg: $1" >&2; exit 2;;
  esac
done

mkdir -p "$OUT"

echo "== preflight (read the rc directly — piping it masks the failure)"
tries=0
until "$GUARD" --check --strict; do
  tries=$((tries + 1))
  if [ "$tries" -ge 30 ]; then
    echo "FATAL: machine is not quiet after 30 tries (60s apart)." >&2; exit 1
  fi
  echo "preflight rc!=0 (try $tries/30) -- transient daemon spike; sleeping 60s"
  sleep 60
done
st="$("$REPO/scripts/isabelle-procs.sh" 2>/dev/null | head -1 || true)"
case "$st" in
  *"nothing running"*) : ;;
  *) echo "FATAL: an Isabelle actor is live — $st" >&2; exit 1 ;;
esac
for f in "$MPS_TABLE" "$AND_TABLE" "$L4_LL" "$H/build/allcomp_bench_l4" \
         "$H/build/all_roots_vs_competitors_bench" "$H/build/cgal_descartes_bench" \
         "$H/build/z3_allroots_timer" "$H/build/pari_timer" "$H/build/libpoly_nosqf_timer" \
         "$H/sage_solve_one_sqf.sage" "$H/sage_solve_multi_sqf.sage" "$H/build/anewdsc_wallclock.dylib" \
         "$REPO/benchmark_results/smt_bench/z3_isolate_timer" "$HOME/Downloads/test_descartes_osx"; do
  [ -e "$f" ] || { echo "FATAL: missing $f" >&2; exit 1; }
done
L4SHA="$(shasum -a 256 "$L4_LL" | cut -d' ' -f1)"
case "$L4SHA" in
  0561bdc3*) : ;;
  *) echo "FATAL: $L4_LL is not the shipped IsaRRI artefact (0561bdc3...): $L4SHA" >&2; exit 1 ;;
esac
echo "   ok  machine quiet, no Isabelle actor, inputs present, IsaRRI artefact 0561bdc3"

if [ ! -s "$PROV" ]; then
  {
    echo "# thesis campaign 2 provenance (docs/THESIS_CAMPAIGN2_PLAN.md, 2026-09-18)"
    echo "# start=$(date -u +%FT%TZ)  host=$(hostname)  $(sysctl -n machdep.cpu.brand_string)"
    echo "# isarri_artifact=$L4SHA  (ship-l4-2026-09-15 = IsaRRI)"
    for b in build/allcomp_bench_l4 build/all_roots_vs_competitors_bench build/cgal_descartes_bench \
             build/z3_allroots_timer build/pari_timer build/pari_realroots_nosqf.dylib \
             build/libpoly_nosqf_timer build/anewdsc_wallclock.dylib anewdsc_wallclock.c \
             sage_solve_one_sqf.sage sage_solve_multi_sqf.sage \
             z3_allroots_timer.cpp pari_timer.c pari_realroots_nosqf.c libpoly_timer.cpp anewdsc_bench.py; do
      echo "# sha16 $(shasum -a 256 "$H/$b" | cut -c1-16)  Dsc/export/c_harness/$b"
    done
    for f in scripts/final-suite-run.py benchmark_results/smt_bench/smt_bench_phase2.py \
             benchmark_results/smt_bench/z3_isolate_timer \
             third_party/root_isolators/libpoly_nosqf/src/upolynomial/root_finding.c; do
      echo "# sha16 $(shasum -a 256 "$REPO/$f" | cut -c1-16)  $f"
    done
    echo "# sha16 $(shasum -a 256 "$HOME/Downloads/test_descartes_osx" | cut -c1-16)  test_descartes_osx (RS-ANewDsc SVN 549)"
    echo "# versions: gp $(echo 'print(version())' | gp -q 2>/dev/null | tr -d '\n'); sage $(sage --version 2>/dev/null | head -1)"
    echo "# git: $(git rev-parse --short HEAD) $(git status --porcelain | wc -l | tr -d ' ') dirty paths"
    echo "# panel=powsub_l4,msolve,anewdsc,anewdsc_i0(-i 0),sagesqf,parisqf,z3sqf(z3 on SMT),cgal,libpolysqf"
    echo "# protocol: MPSolve cap 60 s x 3 reps (no early stop); AND cap 180 s x 2 reps (finished after 1; scored at 150 s); cap on solve time, kill at cap+15 s wall, all arms; rep-major rotated per (case,rep), cell=min of OK reps;"
    echo "#   SMT cap 1 s x 5 reps rotated per (instance,rep); oracle polsturm/analytic (MPSolve/AND), z3 (SMT)"
  } > "$PROV"
fi

caffeinate -dimsu -w $$ &
CAF=$!
trap 'kill "$CAF" 2>/dev/null' EXIT
echo "   ok  caffeinate $CAF bound to pid $$ (dies with this script)"
# 🔴 VERIFY the assertion is held BY OUR OWN caffeinate — do not trust the launch, and do not
# accept somebody else's assertion.  A machine sleep is the one contamination that looks like a
# result (a rep logs 1047s under a 150s cap with status OK, because the monotonic clock froze too),
# and a caffeinate that failed to take is indistinguishable from one that worked until the data is
# already ruined.  ⚠️ A generic "is any sleep assertion held?" check FALSE-PASSES: on this machine
# `powerd` holds PreventUserIdleSystemSleep as "Prevent sleep while display is on", which evaporates
# when the display turns off — i.e. exactly when an overnight leg would sleep.  Match our PID.
# ⚠️ Match it on the PreventSystemSleep line specifically: our pid also appears on the
# display-conditional PreventUserIdleSystemSleep/PreventUserIdleDisplaySleep lines, and those do
# NOT stop idle sleep (2026-09-13: the pid-only grep false-PASSED on exactly those).  Assertion
# registration via powerd can lag ~30 s under load, so the window is 20x3 s, not 5x1 s.
# ⚠️ NO `grep -q` HERE (2026-09-13): this script runs under `set -o pipefail`, and `grep -q`
# exits on first match while pmset is still writing — pmset then dies on SIGPIPE (rc 141) and
# pipefail turns a MATCH into failure. Under load pmset is slow and the race is lost almost
# every time (three consecutive false FATALs). Plain `grep ... >/dev/null` reads to EOF, so no
# SIGPIPE is possible and the rc is grep's match status.
held=0
for _ in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20; do
  if pmset -g assertions 2>/dev/null | grep "pid ${CAF}(caffeinate).*PreventSystemSleep" >/dev/null; then held=1; break; fi
  sleep 3
done
if [ "$held" -ne 1 ]; then
  echo "FATAL: our caffeinate (pid $CAF) holds no assertion — pmset does not list it. A sleep" >&2
  echo "--- pmset diagnostics (is caffeinate alive? under another name?) ---" >&2
  (ps -p "$CAF" -o pid,comm 2>/dev/null; pmset -g assertions 2>/dev/null | head -25) >&2
  echo "       mid-run voids whole ROWS and cannot be repaired by dropping an outlier." >&2
  echo "       (Another process holding one is NOT good enough: powerd's is display-conditional.)" >&2
  exit 1
fi
echo "   ok  pmset lists pid $CAF(caffeinate) holding a sleep assertion"

run_leg() { # run_leg <name> <cmd...>: bounded retries; resume flags make reruns continue
  local name="$1"; shift
  local tries=0 rc=0
  while [ "$tries" -lt 5 ]; do
    tries=$((tries + 1))
    echo "== leg $name (attempt $tries) $(date -u +%FT%TZ)" | tee -a "$LOG"
    # 🔴 Capture rc from the COMMAND, not after the `if`.  A bash `if` whose condition is false and
    # which has no `else` exits 0, so the old `if ...; then ...; fi; echo "exit=$?"` printed
    # `exit=0` for every failure — including the SIGKILL that ended the 2026-09-12 AND leg.  The
    # retry log has to say WHY, or a deliberate pause, an OOM and a driver crash are one event.
    "$@" >>"$LOG" 2>&1; rc=$?
    if [ "$rc" -eq 0 ]; then
      echo "== leg $name DONE $(date -u +%FT%TZ)" | tee -a "$LOG"
      return 0
    fi
    # 🔴 A signal is somebody's DECISION, not a transient fault.  rc >= 128 means the driver was
    # killed (137 = SIGKILL, e.g. scripts/pause-after-leg.sh, an OOM kill, or a human).  Retrying
    # 600s later fights whoever did it — which is exactly what happened on 2026-09-12, where the
    # paused leg was scheduled to resume itself.  Stop and let a person decide.
    if [ "$rc" -ge 128 ]; then
      echo "== leg $name KILLED BY SIGNAL (rc=$rc, signal $((rc - 128))) -- NOT retrying." \
        | tee -a "$LOG"
      echo "   a signal is a decision: resume deliberately with --leg $name (resume-safe)." \
        | tee -a "$LOG"
      return "$rc"
    fi
    echo "== leg $name exit=$rc -- sleeping 600s then resuming (attempt $tries/5)" | tee -a "$LOG"
    sleep 600
  done
  echo "FATAL: leg $name failed 5 attempts -- investigate, then re-invoke (resume-safe)" | tee -a "$LOG"
  return 1
}

case "$LEG" in
  all|mpsolve)
    run_leg mpsolve python3 "$DRIVER" --mode record --campaign2 \
      --cap 60 --reps 3 --full-reps --stop-after-timeouts 3 \
      --table "$MPS_TABLE" --coeffs-dir "$MPS_COEFFS" \
      --out "$OUT/mpsolve_results.csv" || exit 1
    ;;
esac
case "$LEG" in
  all|smt)
    run_leg smt python3 "$SMT_DRIVER" --campaign2 --resume || exit 1
    ;;
esac
case "$LEG" in
  all|and)
    run_leg and python3 "$DRIVER" --mode record --campaign2 \
      --cap 180 --reps 2 --full-reps --stop-after-timeouts 1 \
      --table "$AND_TABLE" --coeffs-dir "$AND_COEFFS" \
      --out "$OUT/and_results.csv" || exit 1
    ;;
esac

echo "ALL LEGS DONE $(date -u +%FT%TZ)" | tee -a "$LOG"
"$REPO/scripts/thesis-campaign-audit.sh" "$OUT" | tee -a "$LOG"
echo "next: python3 ~/Desktop/Thesis/notes/tools/eval_tables.py (campaign 2 sources)" | tee -a "$LOG"

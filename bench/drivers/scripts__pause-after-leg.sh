#!/usr/bin/env bash
# pause-after-leg.sh — stop the campaign pipeline once a named leg completes.
#
# WHY (2026-09-12): the runner chains legs back-to-back with no inter-leg hook,
# and editing a RUNNING shell script is unsafe (bash parses incrementally), so
# the pause is implemented as an external watcher: poll campaign.log for the
# leg's DONE line, then SIGTERM the pipeline group and any stray campaign
# driver. Resume-safe throughout: drivers append/resume by (case,params,solver),
# so killing loses at most the in-flight cell; cells already written are valid
# campaign data and are kept. Worst-case overshoot is a few next-leg cells.
#
# USAGE
#   nohup ./scripts/pause-after-leg.sh <leg> <pipeline-pid> < /dev/null & disown
set -uo pipefail
cd "$(dirname "$0")/.."
REPO="$PWD"
OUT="$REPO/benchmark_results/data/thesis_campaign_2026-09-12"

LEG="${1:?usage: $0 <leg> <pipeline-pid>}"
PIPE_PID="${2:?usage: $0 <leg> <pipeline-pid>}"
POLL=30

echo "watcher pid $$: will pause after leg '$LEG' (pipeline $PIPE_PID)" >>"$OUT/pipeline.log"

while kill -0 "$PIPE_PID" 2>/dev/null; do
  if grep -q "== leg $LEG DONE" "$OUT/campaign.log" 2>/dev/null; then
    break
  fi
  sleep "$POLL"
done

if ! grep -q "== leg $LEG DONE" "$OUT/campaign.log" 2>/dev/null; then
  echo "watcher: pipeline $PIPE_PID died before leg $LEG finished -- nothing to pause" \
    >>"$OUT/pipeline.log"
  exit 0
fi

echo "watcher: leg $LEG DONE -- pausing pipeline $PIPE_PID $(date -u +%FT%TZ)" \
  >>"$OUT/pipeline.log"
# 1. the campaign driver (own session via os.setsid -- SIGTERM lets it reap solvers)
for p in $(ps aux | grep "[f]inal-suite-run.py --mode record --campaign" | awk '{print $2}'); do
  kill "$p" 2>/dev/null && echo "watcher: SIGTERM driver $p" >>"$OUT/pipeline.log"
done
sleep 5
# 2. the pipeline group (runner + supervisor; EXIT traps release their caffeinates)
"$REPO/scripts/bench-guard.sh" --stop "$PIPE_PID" >>"$OUT/pipeline.log" 2>&1 || \
  kill "$PIPE_PID" 2>/dev/null
sleep 3
echo "PAUSED after $LEG $(date -u +%FT%TZ)" > "$OUT/PHASE"
echo "watcher: PHASE=PAUSED; remaining drivers:" >>"$OUT/pipeline.log"
ps aux | grep -E "[f]inal-suite-run.py --mode record --campaign|[t]hesis-pipeline|[t]hesis-campaign" \
  >>"$OUT/pipeline.log" || echo "watcher: none left" >>"$OUT/pipeline.log"

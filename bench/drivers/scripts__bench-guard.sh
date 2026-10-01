#!/usr/bin/env bash
# bench-guard.sh — the ONE preflight/reap predicate for every benchmark in this repo.
#
# WHY THIS EXISTS (2026-08-01, measured, cost ~2 h of discarded work):
#   `pkill -f <driver>` kills the PARENT ONLY. Its in-flight solver child is reparented to
#   init and keeps burning a core. Worse, `subprocess.run(timeout=…)` also kills only the
#   direct child — and `sage` is a wrapper that execs a python worker, while anewdsc_bench.py
#   spawns test_descartes_osx. So EVERY sage/anewdsc timeout leaked a ~100% CPU orphan.
#   Three such orphans (77% + 61% + 100%) inflated every later timing ~1.9x. A pari row read
#   900 ms instead of 469 ms, and the inflation was very nearly attributed to a code change:
#   re-running the UNCHANGED config on the loaded machine reproduced the same 900 ms.
#
#   ⛔ A contaminated benchmark does not look broken. It looks like a result.
#      One orphan invalidates every timing taken after it. ALWAYS preflight.
#
# USAGE
#   scripts/bench-guard.sh --check          # rc=0 clean, rc=1 dirty (prints offenders)
#   scripts/bench-guard.sh --reap           # kill true orphans, then re-check
#   scripts/bench-guard.sh --check --strict # also fail on FOREIGN busy processes
#   scripts/bench-guard.sh --stop <pid>     # stop a driver AND its whole process group
#
# Call --check before the first measurement and --reap after any abnormal stop.
set -uo pipefail

# Exact basenames. ⚠️ Substring matching is WRONG here: /sage/ matches "UsageTrackingAgent"
# and "analyticsagent", which produced two false alarms before this was pinned down.
SOLVER_RE='^(gp|sage|msolve|all_roots_vs_competitors_bench|suite_v2_bench|suite_v2_bench_pre|suite_v2_bench_post|allcomp_bench_l4|allcomp_bench_ship|cgal_descartes_bench|test_descartes_osx|sage_solve_one\.sage\.py|sage_solve_one_sqf\.sage\.py|sage_solve_multi\.sage\.py|sage_solve_multi_sqf\.sage\.py|z3_allroots_timer|z3_isolate_timer|pari_timer|libpoly_timer|libpoly_nosqf_timer)$'
# ⚠️ What "strict" means (user ruling 2026-08-04, replacing the load-average gate): the load
# average is a DECAYING signal — it reads high minutes after the work ended, and blocked the
# campaign while the machine was idle (a 98%-CPU process was OUR OWN classify repro; nothing
# else was busy, yet load read 3.3). What actually contaminates a measurement is a FOREIGN
# process burning CPU RIGHT NOW. So --strict now fails on any process at >= BUSY_CPU % that is
# not one of ours (orchestrator, record driver, or a solver/worker matched above) and not the
# casual UI/system baseline. Load average is printed for information only.
BUSY_CPU="${BENCH_GUARD_BUSY_CPU:-90.0}"
# Sustained-work confirmation (user ruling 2026-09-19): a TRANSIENT spike must never block
# measurement — the alarm fires only when something heavy is RUNNING, i.e. still burning CPU
# a few seconds later. XProtect at ~33% for seconds stalled a launch for 60 s; real
# contaminants (leaked ~100% orphans, another agent's build) persist and still alarm.
# Orphan detection below is unaffected: a leaked solver of ours is always real, transient or not.
SUSTAIN_SECS="${BENCH_GUARD_SUSTAIN_SECS:-5}"
# Per-solver wrapper workers: always legitimate while a driver lives (same rationale as the
# grandchild rule below) — they are named distinctly enough that a foreign copy is not a
# realistic contaminant.
OWN_WORKER_RE='anewdsc_bench\.py|sage_solve_one|sage_solve_multi'
# 🔴 DRIVERS ARE EXCLUDED BY ANCESTRY, NEVER BY NAME (fixed 2026-08-06). Excluding
# `final-suite-run.py` by name made a SECOND, CONCURRENT campaign invisible to --strict — the
# exact contamination AGENTS.md §1b records as having happened here ("the offender was another
# agent running the same plan concurrently"). At PREFLIGHT there is by definition no legitimate
# driver of ours running, so a name-based exclusion is backwards precisely when it matters. A
# driver that INVOKED this check is in our ancestry chain and is skipped; anyone else's is
# reported. (memory: bench-guard-check-is-not-a-quiet-machine)
OWN_DRIVER_RE='final-suite-run\.py|run-calibration-campaign\.py'

# PIDs in this process's ancestry chain — the only drivers that may legitimately be busy.
own_ancestry() {
  local p="$$" guard=0
  while [ -n "$p" ] && [ "$p" -gt 1 ] 2>/dev/null && [ "$guard" -lt 40 ]; do
    printf '%s ' "$p"
    p="$(ps -o ppid= -p "$p" 2>/dev/null | tr -d ' ')"
    guard=$((guard + 1))
  done
}
# The session's UI/system baseline (WindowServer and the host app we run inside) is part of
# the environment, not "other work" — its transient spikes must not block measurement. Real
# foreign compute (>= BUSY_CPU%) is still flagged; another agent's job in a different app is.
UI_RE='^(WindowServer|OpenCode)'
# The operator app hosting the campaign session (a desktop agent client's renderer): its own
# process CPU is UI/session infrastructure, not competing compute — same class as WindowServer.
# Matched on the app-bundle PATH, not the binary name, because a renderer's name can contain a
# space (e.g. "<App> (Renderer)"), which defeats a name match.
# ⚠️ The path list below is UNCHANGED by the 2026-09-06 Codex retirement ON PURPOSE: it exempts
# whichever operator apps run on THIS machine, and dropping an entry makes --strict cry wolf on
# its own host UI (measured 2026-08-06, see below). Removing an app here is a MEASUREMENT change,
# not a docs change.
# Child WORK launched by the app (python/isabelle/clang) is separate processes and still flagged.
# ⚠️ Must list EVERY operator app used on this machine, or --strict cries wolf on its own host
# UI and gets ignored — measured 2026-08-06: with only ChatGPT.app listed, a plain
# `--check --strict` returned rc=1 on an otherwise idle machine because Claude.app's renderer
# sat at 38% CPU. Only the app's OWN binary is skipped; compute it launches (python, isabelle,
# clang) runs as separate processes and is still flagged.
UI_PATH_RE='/Applications/(ChatGPT|Claude)\.app/'
# macOS SYSTEM DAEMONS — same environment class as WindowServer (measured 2026-08-08: six
# `--strict` aborts in ~40 min, all from trustd/ecosystemd/ecosystemanalyticsd spiking to
# 30–70% for seconds then returning to 0%; each spike killed a multi-hour SMT-BENCH campaign).
# They are Apple OS infrastructure, not another agent's compute — real foreign work (python,
# clang, isabelle from another campaign) remains flagged because these daemons are named and
# the exclusion is exact. Deliberately narrow: add a daemon here only after measuring it as a
# recurrent transient offender, never preemptively.
# 2026-09-19: + launchd, airportd, mobileassetd, BackgroundShortcutRunner -- measured as the recurrent
# offenders of the 2026-09-12 campaign (34 blocks in thesis_campaign_2026-09-12/campaign.log: launchd 12,
# airportd 6, BackgroundShortcutRunner 4, mobileassetd 3). Spotlight (Metadata.framework, 7) is NOT
# exempted: indexing is sustained multi-process work, not a transient spike.
SYSTEM_DAEMON_RE='^(trustd|ecosystemd|ecosystemanalyticsd|launchd|airportd|mobileassetd|BackgroundShortcutRunner)$'

# A TRUE orphan is PPID==1. Grandchildren (test_descartes_osx under anewdsc_bench.py, the sage
# worker under the sage wrapper) are legitimate while their driver lives — do NOT flag them.
list_orphans() {
  ps ax -o pid=,ppid=,pcpu=,comm= | awk -v re="$SOLVER_RE" '
    { pid=$1; ppid=$2; cpu=$3; name=$4; sub(/.*\//, "", name)
      if (ppid == 1 && name ~ re) printf "  pid=%-7s cpu=%-6s %s\n", pid, cpu, name }'
}

# python3 orphans are only reportable when running one of our bench WORKERS (the sage worker
# and anewdsc_bench.py both present as bare "python3").
#
# ⚠️ A DRIVER IS NOT AN ORPHAN. `final-suite-run.py` deliberately calls os.setsid(), so its
# PPID is 1 by design — matching it here made --reap kill the very run it exists to protect.
# Caught by testing the guard against a live run; never match driver names.
list_py_orphans() {
  ps ax -o pid=,ppid=,pcpu=,command= | awk '
    { pid=$1; ppid=$2; cpu=$3; $1=$2=$3=""
      if (ppid == 1 && $0 ~ /sage_solve_one|anewdsc_bench/ && $0 !~ /final-suite-run|bench-guard/)
        printf "  pid=%-7s cpu=%-6s %s\n", pid, cpu, substr($0, 4, 90) }'
}

list_busy() {
  ps -Ao pid=,pcpu=,command= | awk -v th="$BUSY_CPU" -v re="$SOLVER_RE" -v worker="$OWN_WORKER_RE" \
      -v drv="$OWN_DRIVER_RE" -v mine="$(own_ancestry)" -v ui="$UI_RE" -v uipath="$UI_PATH_RE" \
      -v sysd="$SYSTEM_DAEMON_RE" '
    BEGIN { n=split(mine, a, " "); for (i=1;i<=n;i++) if (a[i] != "") own[a[i]]=1 }
    { pcpu=$2+0; cmd=$0; sub(/^[[:space:]]*[0-9]+[[:space:]]+[0-9.]+[[:space:]]+/, "", cmd)
      base=cmd; sub(/ .*/, "", base); sub(/.*\//, "", base)
      if (pcpu <= th) next
      if (base ~ re) next                                  # our solver binaries
      if (cmd ~ worker) next                               # our per-solver wrapper workers
      if (cmd ~ drv && ($1 in own)) next                   # a driver in OUR ancestry only
      if (base ~ ui) next                                  # UI/system baseline of this session
      if (base ~ sysd) next                                # measured transient macOS daemons
      if (cmd ~ uipath) next                                 # operator app bundle (see UI_PATH_RE)
      printf "  pid=%-7s cpu=%-6s %s\n", $1, $2, substr(cmd, 1, 90) }'
}

# Re-sample after SUSTAIN_SECS; print only the input lines whose PID is still busy now.
# A transient spike is gone by the second sample and prints nothing (no block).
confirm_sustained() {
  local first="$1" pids pat second
  pids="$(printf '%s\n' "$first" | sed -E 's/^ *pid=([0-9]+).*/\1/' | tr '\n' ' ')"
  [ -z "${pids// /}" ] && return 0
  sleep "$SUSTAIN_SECS"
  second="$(list_busy)"
  [ -z "$second" ] && return 0
  pat="pid=($(printf '%s' "$pids" | tr -s ' ' '|' | sed 's/|$//'))([^0-9]|$)"
  printf '%s\n' "$second" | grep -E "$pat" || true
}

do_check() {
  local strict="${1:-}" bad=0
  local orph py
  orph="$(list_orphans)"; py="$(list_py_orphans)"
  if [ -n "$orph$py" ]; then
    echo "⛔ ORPHANED SOLVER PROCESSES — any timing taken now is CONTAMINATED:"
    [ -n "$orph" ] && echo "$orph"
    [ -n "$py" ] && echo "$py"
    echo "   reap with: scripts/bench-guard.sh --reap"
    bad=1
  fi
  if [ "$strict" = "--strict" ]; then
    # Actual-CPU check (not the decaying load average): a FOREIGN process burning >= BUSY_CPU%
    # right now is what actually contaminates a measurement. Our own campaign processes are
    # excluded (a check must not flag the run it guards — the orchestrator, the record driver,
    # and every solver/worker it spawns are all legitimate at the moment the check runs).
    local busy la
    busy="$(list_busy)"
    la="$(sysctl -n vm.loadavg | awk '{print $2}')"
    if [ -n "$busy" ]; then
      busy="$(confirm_sustained "$busy")"
    fi
    if [ -n "$busy" ]; then
      echo "⛔ FOREIGN WORK BURNING CPU NOW (>= ${BUSY_CPU}%, load $la):"
      echo "$busy"
      echo "   nothing else may run while we measure — stop it or wait."
      bad=1
    else
      echo "   (load average $la — informational only; no foreign process is busy now)"
    fi
  fi
  [ "$bad" -eq 0 ] && echo "✅ machine clean — safe to measure"
  return $bad
}

case "${1:---check}" in
  --check) do_check "${2:-}" ;;
  --reap)
    pids="$(list_orphans | sed 's/.*pid=\([0-9]*\).*/\1/'; list_py_orphans | sed 's/.*pid=\([0-9]*\).*/\1/')"
    if [ -z "$pids" ]; then echo "no orphans to reap"; else
      for p in $pids; do kill -9 "$p" 2>/dev/null && echo "  killed $p"; done
      sleep 2
    fi
    do_check "${2:-}" ;;
  --stop)
    pid="${2:?usage: --stop <pid>}"
    pgid="$(ps -o pgid= -p "$pid" 2>/dev/null | tr -d ' ')"
    if [ -n "$pgid" ]; then kill -- "-$pgid" 2>/dev/null; echo "stopped process group $pgid"; else
      echo "no such pid $pid"; fi
    sleep 2; do_check ;;
  *) sed -n '2,30p' "$0"; exit 2 ;;
esac

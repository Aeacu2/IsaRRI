#!/usr/bin/env bash
# isabelle-procs.sh — the ONE definition of "is an Isabelle build running?".
#
# Dual mode:
#   source scripts/isabelle-procs.sh   -> defines isa_* functions (no side effects, fail-open)
#   scripts/isabelle-procs.sh          -> prints the report; exit 0 = something live, 1 = clear
#
# ---------------------------------------------------------------------------------------
# WHY THIS FILE EXISTS (2026-07-24 — a REPORTED false negative, reproduced and root-caused).
#
# status.sh printed "Is a build running? -> no" while a poly process sat at 99.8% CPU. Every
# caller in the repo used the same predicate:
#       ps -Ao command | grep -q "[I]sabelle_Tool build"
# That string exists ONLY in the JVM DRIVER's argv — two processes, the `lib/Tools/java` bash
# wrapper and its java child, both carrying `isabelle.Isabelle_Tool build …`. The process that
# actually burns the CPU and WRITES THE HEAPS is the Poly/ML worker,
#       <isabelle>/contrib/polyml-*/<plat>/poly -q --minheap 500 … loadHierarchy […]
# whose argv contains no such string (verified against a live build, 2026-07-24).
#
# So the instant the JVM driver dies while the ML worker lives — which is EXACTLY the state
# produced by the Bash-tool ~120 s SIGTERM that CLAUDE.md §0 names as the top hazard, and by
# any interrupted or detached build — every caller read "no build running":
#   * status.sh / session-brief.sh report a clear board that is not clear (the reported bug);
#   * assert_no_build_running (check.sh / export.sh / freeze-base.sh) lets a
#     SECOND build start against a heap dir a live ML worker is still writing — precisely the
#     concurrent-writer case that guard exists to prevent;
#   * backup_base_heaps.sh cheerfully snapshots a heap mid-write.
# The whole contention discipline rests on this check, so it must not have a blind spot.
#
# The converse hole is just as real: keying ONLY on poly (run_watched and safe-kill-build.sh
# did, as did the since-deleted keep_going.sh) misses a build still in its JVM/dependency-resolution phase — no ML
# worker exists yet — and mis-reads an interactive jEdit session as a build.
#
# Therefore: detect BOTH families and report WHICH. An orphaned ML worker is a different
# problem from a healthy build (it needs safe-kill-build.sh, not patience), and every caller
# needs to tell them apart.
#
# Self-matching: every pattern below uses the bracket idiom ([I]sabelle, [p]olyml) so the grep
# in the pipeline can never match its own argv — the dev_guard rule-12 trap.
# ---------------------------------------------------------------------------------------

# Guard against double-sourcing (check.sh sources _common.sh which sources this).
if [ -z "${_ISA_PROCS_SOURCED:-}" ]; then
_ISA_PROCS_SOURCED=1

# The JVM driver of a build: `… isabelle.Isabelle_Tool build …`.
_ISA_DRIVER_RE='[I]sabelle_Tool[[:space:]]+build([[:space:]]|$)'
# An interactive jEdit session — also holds an ML worker, but is NOT a build.
_ISA_JEDIT_RE='[I]sabelle_Tool[[:space:]]+jedit|[j]edit\.JEdit'
# A headless PIDE MCP server (kappelmann/isabelle-pide-mcp, registered as an Isabelle
# component 2026-09-05). Like jEdit it holds an ML worker WITHOUT a build driver, so without
# this pattern isa_state() reads `ml-orphan` — the state whose advice is "a build was
# SIGTERM'd, kill it via safe-kill-build.sh". It is neither orphaned nor killable that way:
# it is a live agent session, and its `start_session` tool calls Build.build(build_heap=true),
# which is why every non-`none` state still blocks a build (CLAUDE.md rule 2, ONE actor).
#
# 🔴 MATCH THE INVOCATION, NEVER THE JAR (fixed 2026-09-08). This pattern used to carry a
# second alternative `[i]sabelle_pide_mcp\.jar`, and registering the component with
# `isabelle components -u` puts that jar on the classpath of EVERY Isabelle Scala JVM — so
# it matched every `isabelle build`, not just the server. Two consequences, the second
# serious: a plain build printed a spurious PIDEMCP line, and an ML worker with NO driver
# (a SIGTERM'd build — precisely the orphan safe-kill-build.sh exists to recover) would
# read `pide-mcp` instead of `ml-orphan` whenever any Isabelle JVM was alive, at which
# point safe-kill-build.sh REFUSES the kill and the documented recovery path is disarmed.
# Verified 2026-09-08: the fastloop build's own JVM matched the jar alternative, while all
# three live MCP processes match the invocation alternative below. Keep it that way.
_ISA_PIDE_MCP_RE='[I]sabelle_Tool[[:space:]]+pide_mcp'
# The Poly/ML worker: the Isabelle-bundled poly binary. Matched by PATH, not by `--minheap`,
# so a changed ML_OPTIONS cannot silently blind the check.
_ISA_ML_RE='contrib/[p]olyml-[^ ]*/poly[[:space:]]'
# …minus the ml_statistics satellite, which is a monitor of a worker, not a worker.
_ISA_ML_EXCL_RE='ml_statistics|ML_Statistics'

# isa_scan — take ONE ps snapshot; all getters below read it. Call to refresh.
# DSC_ISA_PS_FIXTURE=<file> substitutes a canned snapshot: the states that matter most here
# (an orphaned ML worker, a driver with no worker yet) are the ones you cannot conjure on
# demand without killing a real build, so they would otherwise go untested forever.
isa_scan() {
  if [ -n "${DSC_ISA_PS_FIXTURE:-}" ] && [ -r "${DSC_ISA_PS_FIXTURE:-}" ]; then
    _ISA_SNAP="$(cat "$DSC_ISA_PS_FIXTURE" 2>/dev/null || true)"
  else
    _ISA_SNAP="$(ps -Ao pid=,pcpu=,etime=,command= 2>/dev/null || true)"
  fi
  return 0
}
_isa_snap() {
  [ -n "${_ISA_SNAP:-}" ] || isa_scan
  printf '%s\n' "${_ISA_SNAP:-}"
}

isa_driver_lines() { _isa_snap | grep -E "$_ISA_DRIVER_RE" || true; }
isa_jedit_lines()  { _isa_snap | grep -E "$_ISA_JEDIT_RE"  || true; }
isa_pide_mcp_lines() { _isa_snap | grep -E "$_ISA_PIDE_MCP_RE" || true; }
isa_ml_lines()     { _isa_snap | grep -E "$_ISA_ML_RE" | grep -vE "$_ISA_ML_EXCL_RE" || true; }

# isa_ml_pids — pids of the ML workers, newest last. The kill target for safe-kill-build.sh.
isa_ml_pids() { isa_ml_lines | awk '{print $1}' || true; }

# isa_state — one word describing the machine, refreshed on each call:
#   none           nothing Isabelle-ish is running
#   build          a healthy build: JVM driver + ML worker
#   build-starting a build whose JVM is up but whose ML worker has not spawned yet
#   ml-orphan      an ML worker with NO driver -> THE case the old predicate could not see:
#                  a SIGTERM'd/detached build still holding CPU and possibly mid-heap-write
#   jedit          an interactive jEdit session (ML worker + jedit driver), not a build
#   pide-mcp       a headless PIDE MCP server holding a live agent session (or building one
#                  IN-PROCESS: its start_session calls Build.build(build_heap=true), which
#                  spawns ML workers but NO `Isabelle_Tool build` driver)
isa_state() {
  isa_scan
  local drv ml jed mcp
  drv="$(isa_driver_lines)"; ml="$(isa_ml_lines)"; jed="$(isa_jedit_lines)"
  mcp="$(isa_pide_mcp_lines)"
  if [ -n "$drv" ]; then
    [ -n "$ml" ] && { echo build; return 0; }
    echo build-starting; return 0
  fi
  if [ -n "$ml" ]; then
    [ -n "$jed" ] && { echo jedit; return 0; }
    [ -n "$mcp" ] && { echo pide-mcp; return 0; }
    echo ml-orphan; return 0
  fi
  # An MCP server with NO session is deliberately NOT a state: it is a JVM holding no ML
  # worker and no heap, so it cannot contend. Making it non-`none` would trip
  # assert_no_build_running (_common.sh) on every check.sh for the whole time the agent's
  # server is up — i.e. always. isa_report still prints it, so it stays visible.
  echo none
}

# isa_running — rc 0 iff ANY Isabelle process holds the heap dir / the CPU.
# This is the predicate to gate a new build on: every non-`none` state is a reason not to
# start a second one (they all share the ONE user heap dir — CLAUDE.md §0).
isa_running() { [ "$(isa_state)" != "none" ]; }

# isa_report [indent] — human-readable detail. Prints nothing when the machine is clear.
isa_report() {
  local ind="${1:-  }" line pid cpu et cmd sess
  isa_scan
  # ONE build shows up as TWO driver processes (the lib/Tools/java bash wrapper and its java
  # child, same argv tail), so dedupe on the session being built — otherwise every build is
  # reported twice and reads like two concurrent builds, the opposite of the point here.
  isa_driver_lines | while IFS= read -r line; do
    [ -n "$line" ] || continue
    pid="$(printf '%s' "$line" | awk '{print $1}')"
    et="$(printf '%s' "$line" | awk '{print $3}')"
    # the session being built is the `-b <S>` argument, else the trailing token
    sess="$(printf '%s' "$line" | grep -oE -- '-b +[A-Za-z0-9_]+' | tail -1 | awk '{print $2}')"
    [ -n "$sess" ] || sess="$(printf '%s' "$line" | awk '{print $NF}')"
    printf '%sDRIVER  session=%-38s pid=%-6s elapsed=%s\n' "$ind" "$sess" "$pid" "$et"
  done | awk '!seen[$2]++'
  isa_ml_lines | while IFS= read -r line; do
    [ -n "$line" ] || continue
    pid="$(printf '%s' "$line" | awk '{print $1}')"
    cpu="$(printf '%s' "$line" | awk '{print $2}')"
    et="$(printf '%s' "$line" | awk '{print $3}')"
    printf '%sML      pid=%-6s elapsed=%-12s cpu=%s%%\n' "$ind" "$pid" "$et" "$cpu"
  done
  # The PIDE MCP server: reported even with no ML worker (state `none`), because "an agent
  # server is up" is what explains an ML worker appearing without a build driver later.
  isa_pide_mcp_lines | while IFS= read -r line; do
    [ -n "$line" ] || continue
    pid="$(printf '%s' "$line" | awk '{print $1}')"
    et="$(printf '%s' "$line" | awk '{print $3}')"
    # ONE server is TWO processes (the lib/Tools/java bash wrapper and its java child), same
    # as a build driver — dedupe on the option tail so it does not read as two servers.
    sess="$(printf '%s' "$line" | sed -n 's/.*pide_mcp//p' | tr -s ' ')"
    printf '%sPIDEMCP opts=%-24s pid=%-6s elapsed=%s\n' "$ind" "${sess:--}" "$pid" "$et"
  done | awk '!seen[$2]++'
  return 0
}

# isa_base_heap_recently_written — true iff a FROZEN BASE heap was modified in the last 3 min.
# The precondition on every kill decision: a killed LEAF heap self-heals, a BASE truncated
# mid-write is the ~30-min-rebuild disaster (CLAUDE.md §0).
#
# NB the PARENTHESISED -o group. `find A -o -name B -mmin -3` applies -mmin to the LAST clause
# only; that precedence bug produced a false "safe to kill" reading on 2026-07-10 (it printed a
# match while the caller reported "empty above"). Lives here, in ONE place, because it used to
# be copy-pasted into _common.sh AND safe-kill-build.sh — two copies of a subtle find(1)
# expression is how the fixed one silently drifts back to the broken one.
isa_base_heap_recently_written() {
  local dirs=() d
  for d in "$HOME/.isabelle"/*/heaps/*/ /Applications/Isabelle2025-2.app/heaps/*/; do
    [ -d "$d" ] && dirs+=("$d")
  done
  [ "${#dirs[@]}" -eq 0 ] && return 1
  find "${dirs[@]}" -maxdepth 1 \
       \( -name 'Dsc_Spec' -o -name 'Dsc_LLVM_Base' -o -name 'Dsc_LLVM_Shared_Base' \) \
       -mmin -3 2>/dev/null | grep -q .
}

# isa_state_advice <state> — the one-line "so what do I do" for a state.
isa_state_advice() {
  case "$1" in
    build)          echo "a build is running — do NOT start another (another agent may own it)" ;;
    build-starting) echo "a build is starting (JVM up, ML worker not spawned yet) — do NOT start another" ;;
    ml-orphan)      echo "ORPHANED ML worker: a poly process with NO build driver. A build was SIGTERM'd/detached and its ML worker is STILL running — it holds the CPU and may be mid-heap-write. Do not start a build. Check 'scripts/status.sh'; terminate it ONLY via 'scripts/safe-kill-build.sh' (it refuses while a base heap is being written), then re-check for a wiped row (CLAUDE.md §0)" ;;
    pide-mcp)       echo "a PIDE MCP server holds a LIVE session, or is building one in-process (ML worker, no build driver). NOT an orphan and NOT a safe-kill-build.sh target — killing it kills an agent session, not a stuck build. It shares the ONE user heap dir, so do not start a build against it: stop the session with the MCP's stop_session tool first (CLAUDE.md rule 2, ONE actor)" ;;
    jedit)          echo "an interactive jEdit session is open — it shares the ONE user heap dir, so a build now can race it (CLAUDE.md §0). Close it or accept the risk" ;;
    *)              echo "clear" ;;
  esac
}

fi  # _ISA_PROCS_SOURCED

# ---- standalone mode: print the report ------------------------------------------------
# `return` fails outside a sourced file, which is exactly how we tell the two apart.
if ! (return 0 2>/dev/null); then
  _st="$(isa_state)"
  if [ "$_st" = "none" ]; then
    echo "isabelle: nothing running (no build driver, no ML worker)"
    exit 1
  fi
  echo "isabelle: $_st — $(isa_state_advice "$_st")"
  isa_report "  "
  exit 0
fi
:

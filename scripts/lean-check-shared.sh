#!/usr/bin/env bash
# scripts/lean-check-shared.sh — lean-check for many agents sharing one daemon.
#
# Same request as scripts/lean-check.sh, with three differences that keep a shared daemon
# (docker/docker-compose.shared.yml) usable:
#  - one request at a time: a flock around each request, since the daemon serialises
#    anyway and drops connections beyond its listen backlog of 4;
#  - an empty answer (a dropped connection, a restart) is retried;
#  - a closed port is waited for, never answered by starting a second Lean process
#    (lean-check.sh's fallback would, and two Lean processes overcommit this box).
#
# Usage: scripts/lean-check-shared.sh <file.lean>   (LEAN_CHECK_WAIT, default 1800 s)
set -euo pipefail
FILE="${1:?usage: $0 <file.lean>}"
[[ -f "$FILE" ]] || { echo "[lean-check-shared] file not found: $FILE" >&2; exit 2; }
HOST=127.0.0.1 PORT=7878 LOCK="${LEAN_CHECK_LOCK:-/tmp/mathfin-lean-repl.lock}"
WAIT="${LEAN_CHECK_WAIT:-1800}"
# The daemon elaborates with autoImplicit on and the build has it off; check like the build
# (error line numbers after the imports shift by one).
BODY="$(mktemp)"; trap 'rm -f "$BODY"' EXIT
last=$(grep -nE '^(public )?import ' "$FILE" | tail -1 | cut -d: -f1 || true)
awk -v n="${last:-0}" '{print} NR==n{print "set_option autoImplicit false"}' "$FILE" > "$BODY"
[[ -n "$last" ]] || { echo "set_option autoImplicit false"; cat "$FILE"; } > "$BODY"
deadline=$(( $(date +%s) + WAIT ))
while :; do
  if { exec 3<>"/dev/tcp/$HOST/$PORT"; } 2>/dev/null; then
    exec 3>&-
    out="$(flock "$LOCK" nc -N "$HOST" "$PORT" < "$BODY" || true)"
    if [[ -n "$out" ]]; then printf '%s\n' "$out"; exit 0; fi
    echo "[lean-check-shared] empty answer, retrying" >&2
  else
    echo "[lean-check-shared] daemon not up on $HOST:$PORT, waiting" >&2
  fi
  (( $(date +%s) < deadline )) || { echo "[lean-check-shared] gave up after ${WAIT}s" >&2; exit 3; }
  sleep 15
done

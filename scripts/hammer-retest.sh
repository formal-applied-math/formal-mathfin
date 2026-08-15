#!/usr/bin/env bash
# The LeanHammer re-test, run INSIDE the pinned verify container.
#
# The 2026-06-06 pilot scored 0/10 kernel-accepted but ran hammer one Lean
# version off its target, and its own report blames that skew. LeanHammer main
# has targeted our v4.32.0 since 2026-07-14, so this is the first fair run.
# Baseline to beat and the adoption criteria: docs/hammer-pilot-2026-06-06.md.
#
# Invoked by .github/workflows/hammer-retest.yml. Not for the dev box — the
# memory doctrine puts full-environment batch work on GitHub runners.
#
# Inputs (env):  HAMMER_REV, PILOTS ("A" | "A+B" | "A+B+C"), TMO (sec/file)
# Outputs:       /out/results.tsv, /out/<pilot>.log, /out/blocked.txt on a
#                dependency failure.
#
# NOTE: failures are the DATA here, so this never `set -e`s over a pilot run.
# It exits 0 even when hammer fails; the workflow reads results.tsv.
set -uo pipefail

APP="${APP_DIR:-/app}"
WORK="${WORK_DIR:-/work}"     # the repo checkout (read-only): scripts + pilots
OUT="${OUT_DIR:-/out}"
HAMMER_REV="${HAMMER_REV:-a841fded}"
PILOTS="${PILOTS:-A+B}"
TMO="${TMO:-1800}"

mkdir -p "$OUT"
cd "$APP" || { echo "no $APP"; exit 1; }

# `lake update` rewrote lean-toolchain during the 2026-06-06 pilot.
cp lean-toolchain /tmp/toolchain.bak

if ! python3 "$WORK/scripts/hammer_lakefile_patch.py" "$HAMMER_REV"; then
  echo "lakefile patch failed" > "$OUT/blocked.txt"; exit 0
fi

echo "[retest] lake update Hammer @ $HAMMER_REV"
lake update Hammer > "$OUT/update.log" 2>&1
tail -25 "$OUT/update.log"

if ! diff -q /tmp/toolchain.bak lean-toolchain >/dev/null 2>&1; then
  echo "[retest] WARNING: lake update rewrote lean-toolchain — restoring"
  cp /tmp/toolchain.bak lean-toolchain
fi
OURS="$(cat lean-toolchain)"
THEIRS="$(cat .lake/packages/Hammer/lean-toolchain 2>/dev/null || echo unknown)"
echo "[retest] ours=$OURS  hammer=$THEIRS"
if [ "$OURS" != "$THEIRS" ]; then
  # This is the exact confound that invalidated the 2026-06-06 run. Refuse to
  # repeat it: a skewed result is worse than no result, because it gets cited.
  printf 'toolchain skew: ours=%s hammer=%s — this is the 2026-06-06 confound, refusing to run\n' \
    "$OURS" "$THEIRS" > "$OUT/blocked.txt"
  cat "$OUT/blocked.txt"; exit 0
fi

# NEVER pipe a build log you are diagnosing into `tail` — the FIRST error is
# the diagnostic one, and the 2026-08-15 run lost every per-target failure
# message that way, leaving only Lake's closing summary. Full log to the
# artifact; on failure surface the EARLIEST errors.
echo "[retest] lake build Hammer (full log -> build.log)"
timeout 5400 lake build Hammer > "$OUT/build.log" 2>&1
BUILD=$?
grep -c . "$OUT/build.log" >/dev/null 2>&1 || true
if [ "$BUILD" -ne 0 ]; then
  {
    echo "Hammer cluster did not build (exit $BUILD)"
    echo
    echo "first errors:"
    grep -nEi "error|failed|cannot|no such|not found|denied|unsupported" "$OUT/build.log" \
      | grep -v "^.*Some required targets logged failures" | head -40
  } > "$OUT/blocked.txt"
  cat "$OUT/blocked.txt"
  exit 0
fi

# PilotA pins {disableGrind := true}. The kernel rejection the pilot hit came
# from hammer's GRIND driver, so the committed file never exercises it —
# generate the default-config variant so the re-test actually covers it.
mkdir -p "$APP/tests/hammer_pilot"
cp "$WORK"/tests/hammer_pilot/Pilot*.lean "$APP/tests/hammer_pilot/"
sed 's/ {disableGrind := true}//g' "$APP/tests/hammer_pilot/PilotA.lean" \
  > "$APP/tests/hammer_pilot/PilotA_default.lean"

case "$PILOTS" in
  A)     FILES="PilotA PilotA_default" ;;
  A+B)   FILES="PilotA PilotA_default PilotB" ;;
  *)     FILES="PilotA PilotA_default PilotB PilotC" ;;
esac

: > "$OUT/results.tsv"
for f in $FILES; do
  echo "[retest] === $f (timeout ${TMO}s)"
  START=$(date +%s)
  timeout "$TMO" lake env lean "tests/hammer_pilot/$f.lean" > "$OUT/$f.log" 2>&1
  RC=$?
  ELAPSED=$(( $(date +%s) - START ))
  # `grep -c` exits 1 on zero matches and prints 0 — capture the number, not the
  # exit status (a silent grep is not a clean grep).
  KERNEL=$(grep -c '(kernel)' "$OUT/$f.log"); KERNEL=${KERNEL:-0}
  SORRY=$(grep -c 'declaration uses' "$OUT/$f.log"); SORRY=${SORRY:-0}
  ERRORS=$(grep -c 'error:' "$OUT/$f.log"); ERRORS=${ERRORS:-0}
  if   [ "$RC" -eq 124 ]; then VERDICT=TIMEOUT
  elif [ "$RC" -eq 0 ] && [ "$ERRORS" -eq 0 ]; then VERDICT=CLEAN
  else VERDICT=FAILED; fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$VERDICT" "$ELAPSED" "$KERNEL" "$SORRY" "$ERRORS" \
    >> "$OUT/results.tsv"
  echo "[retest] $f: $VERDICT in ${ELAPSED}s (kernel=$KERNEL sorry=$SORRY errors=$ERRORS)"
  tail -25 "$OUT/$f.log"
done

echo "[retest] done"

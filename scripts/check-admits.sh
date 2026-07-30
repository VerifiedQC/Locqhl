#!/usr/bin/env bash
# check-admits.sh — regression gate on incomplete proofs.
#
# Counts `Admitted.` and the `admit` tactic across Core/ and fails if the total
# exceeds the committed baseline, or if any admit appears OUTSIDE the file(s)
# where open proofs are expected. This lets the known-in-progress proofs stay
# while preventing NEW admits from sneaking in (esp. into files 1-9, which are
# meant to be complete).
#
# Baseline is stored in scripts/admit-baseline.txt (a single integer).
# When you discharge an admit, lower the baseline in the same commit.
set -euo pipefail

cd "$(dirname "$0")/.."

SRC_DIR="Core"
BASELINE_FILE="scripts/admit-baseline.txt"
# Files where open proofs are currently tolerated (the soundness development).
ALLOWED_OPEN="Core/Soundness.v"

baseline=$(tr -d '[:space:]' < "$BASELINE_FILE")

# Count `Admitted.` and the `admit` tactic (word-boundary, ignore "admit" in comments is best-effort).
admitted=$(grep -rhoE '\bAdmitted\.' "$SRC_DIR" | wc -l | tr -d ' ')
admits=$(grep -rhoE '\badmit\b' "$SRC_DIR" | wc -l | tr -d ' ')
total=$((admitted + admits))

echo "== admit gate =="
echo "Admitted.        : $admitted"
echo "admit (tactic)   : $admits"
echo "total            : $total"
echo "baseline (max)   : $baseline"

status=0

# 1) No admits allowed outside the tolerated file(s).
stray=$(grep -rlE '\bAdmitted\.|\badmit\b' "$SRC_DIR" | grep -vxF "$ALLOWED_OPEN" || true)
if [ -n "$stray" ]; then
  echo "FAIL: admits found outside $ALLOWED_OPEN:"
  echo "$stray" | sed 's/^/  - /'
  status=1
fi

# 2) Total must not exceed baseline.
if [ "$total" -gt "$baseline" ]; then
  echo "FAIL: admit total $total exceeds baseline $baseline (new incomplete proofs introduced)."
  status=1
elif [ "$total" -lt "$baseline" ]; then
  echo "NOTE: admit total $total is below baseline $baseline — nice. Please lower $BASELINE_FILE to $total."
fi

if [ "$status" -eq 0 ]; then
  echo "OK: admit gate passed."
fi
exit $status

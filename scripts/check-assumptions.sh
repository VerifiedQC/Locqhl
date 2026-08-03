#!/usr/bin/env bash
# check-assumptions.sh — AUTHORITATIVE proof-status check.
#
# scripts/manifest.sh is source-level: it sees `Qed.` vs `Admitted.` but cannot
# tell whether a Qed-closed lemma transitively DEPENDS on an admitted one. This
# script closes that gap by running Rocq's `Print Assumptions` on every lemma the
# manifest calls "proven", and failing if any admitted lemma leaks into the
# dependency cone of a supposedly-proven result.
#
# It also reports the set of axioms the mechanization relies on — the standard
# classical-reals / functional-extensionality axioms inherited from QuantumLib
# and Rocq's stdlib. Paper mechanization claims should disclose these.
#
# Requires a BUILT tree (.vo files present), i.e. run after `make`:
#   make && bash scripts/check-assumptions.sh
# or inside the pinned image:
#   docker run --rm locqhl:9.1 bash -lc 'bash scripts/check-assumptions.sh'
set -euo pipefail
cd "$(dirname "$0")/.."

MODULE="${1:-Soundness}"

# Names the manifest reports as proven, in the target module.
names=$(bash scripts/manifest.sh | grep "Core/${MODULE}.v" \
        | awk -F'|' '$6 ~ /proven/ {n=$5; gsub(/ /,"",n); print n}')

if [ -z "$names" ]; then
  echo "No proven lemmas found in Core/${MODULE}.v — nothing to check."
  exit 0
fi

query=$(mktemp)
{
  echo "From Locqhl.Core Require Import ${MODULE}."
  while IFS= read -r n; do [ -n "$n" ] && echo "Print Assumptions ${n}."; done <<< "$names"
} > "$query"

out=$(mktemp)
rocq repl -R third_party/QuantumLib QuantumLib -Q Core Locqhl.Core < "$query" > "$out" 2>&1 || true

count=$(grep -c 'Print Assumptions' "$query" || true)
echo "== assumption check: Core/${MODULE}.v =="
echo "proven lemmas checked : $count"

status=0

if grep -q '^Error' "$out"; then
  echo "FAIL: Rocq reported an error (is the tree built? run make first):"
  grep -n '^Error' "$out" | head -5
  status=1
fi

# Any lemma the manifest calls admitted must NOT appear as an assumption of a
# proven lemma.
admitted=$(bash scripts/manifest.sh | grep "Core/${MODULE}.v" \
           | awk -F'|' '$6 ~ /admitted/ {n=$5; gsub(/ /,"",n); print n}')
leak=0
while IFS= read -r a; do
  [ -z "$a" ] && continue
  if grep -qE "(^|[^A-Za-z_])${a}([^A-Za-z_]|$)" "$out"; then
    echo "FAIL: admitted lemma '${a}' leaks into a proven lemma's assumptions."
    leak=1
  fi
done <<< "$admitted"
[ "$leak" -eq 0 ] && echo "no admitted lemma leaks into any proven result: OK"
[ "$leak" -ne 0 ] && status=1

echo "-- axioms relied upon --"
grep -E "^[A-Za-z][A-Za-z0-9_.']*  *:" "$out" | sed 's/ *:.*//' | sort -u | sed 's/^/  /'

rm -f "$query" "$out"
exit $status

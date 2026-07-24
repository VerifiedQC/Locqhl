#!/usr/bin/env bash
# manifest.sh — emit a manifest of every Lemma/Theorem/Corollary/Definition in
# Core/, with file:line, kind, name, and proof status.
#
# STATUS is derived by scanning from each statement to its terminator:
#   Qed. / Defined.  -> proven
#   Admitted.        -> admitted
#   (contains `admit` before terminator) -> has-admit
# Definitions/Fixpoints/Inductives are reported as `def`.
#
# NOTE (v0, source-level): this sees SYNTACTIC admits only. It cannot detect a
# lemma that is closed with Qed but transitively DEPENDS on an admitted lemma.
# The authoritative manifest comes from `Print Assumptions <thm>.` after a real
# Rocq 9.1 build (see CI). Use this as a fast, build-free correspondence-table
# input; treat "proven" as "locally Qed-closed".
#
# Portability: avoids awk `\b` (unsupported by BSD/macOS awk); uses line anchors.
set -euo pipefail
cd "$(dirname "$0")/.."

printf '| file | line | kind | name | status |\n'
printf '| --- | --- | --- | --- | --- |\n'

for f in Core/*.v; do
  awk -v file="$f" '
    function flush(status) {
      if (name != "") printf("| %s | %d | %s | %s | %s |\n", file, hdr_line, kind, name, status);
      name=""; kind=""; hdr_line=0; seen_admit=0;
    }
    function ident(kw) {
      match($0, kw "[[:space:]]+[A-Za-z0-9_'"'"']+");
      t=substr($0, RSTART, RLENGTH); sub(/^[A-Za-z]+[[:space:]]+/, "", t); return t;
    }
    # Statement headers that carry a proof obligation.
    /^[[:space:]]*(Lemma|Theorem|Corollary|Proposition|Example)[[:space:]]/ {
      if (name != "") flush("open?");
      kind="lemma"; hdr_line=NR; seen_admit=0;
      name=ident("(Lemma|Theorem|Corollary|Proposition|Example)"); next;
    }
    # Non-proof definitions.
    /^[[:space:]]*(Definition|Fixpoint|Instance|Inductive|Record)[[:space:]]/ {
      if (name != "") flush("open?");
      printf("| %s | %d | def | %s | def |\n", file, NR, ident("(Definition|Fixpoint|Instance|Inductive|Record)"));
      name=""; next;
    }
    # Track an `admit` tactic in the current proof body (lowercase; "Admitted" does not match).
    name != "" && /(^|[^A-Za-z])admit([^A-Za-z]|$)/ { seen_admit=1 }
    # Terminators (may be at line start or mid-line, e.g. one-line `Proof. .. Qed.`).
    name != "" && /(^|[[:space:]])Admitted\./       { flush("admitted"); next }
    name != "" && /(^|[[:space:]])(Qed|Defined)\./  { flush(seen_admit ? "has-admit" : "proven"); next }
    END { if (name != "") flush("open?") }
  ' "$f"
done

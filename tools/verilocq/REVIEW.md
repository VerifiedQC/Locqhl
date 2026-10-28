# VeriLocQ review summary

Condensed record of the independent implementation reviews of VeriLocQ
(v0.2 through v0.8.0, then the PR #18 review at `1a5805f`). The full
chronological log is in git history: `git show 1a5805f:tools/verilocq/REVIEW.md`.

## Soundness findings fixed (each has a regression test)

High severity — each could produce a false `VERIFIED`:

- Distillation: post-processing a measurement record (`mA := 1 - mA`) left the
  proof valid although the controller accepted different physical outcomes.
  Stored records are now bound to the recorded physical outcomes.
- Distillation: the proof horizon `n` could be owned and assigned by a process.
  `n` is now an immutable external parameter.
- Distillation: a weakened user invariant with unconditional acceptance bypassed
  the quantum-selector reasoning. The invariant must now imply the canonical
  selector facts, and termination below the horizon must imply equal outcomes.
- Indexed proofs: a finite-sum binder kept an ambient assumption on the same
  symbol, making the context inconsistent; binders are now scoped.
- Hoare replay: expression-valued outcomes were accepted as logical variables
  (e.g. `{true; I} mA:=0 {false; I}`), and a constant ranking variable made
  decrease premises vacuous. Fresh zero-arity constants are now required.
- Hoare replay: a SymPy `Dummy` named `kA` could alias the source counter;
  index translation now preserves symbol identity.
- Hoare replay: textual SMT cache keys conflated sorts, so a rejected proof
  could poison the cache. Keys now use live Z3 AST identity, and inputs are
  validated before memoization.

Medium/low severity: a public implication check accepted inconsistent domain
declarations; the teleportation channel audit fixed scratch inputs; failed
protocols could export distillation bounds; the schema ignored changed array
layouts; unknown predicate kinds passed under false guards; generic gate powers
were reduced modulo two; deep sequential blocks hit Python recursion limits;
plus several report/JSON presentation fixes.

## Validation

- Independent checks at each snapshot: exact PSD checker vs. principal-minor
  criterion on 300 random rational Hermitian matrices; Pauli-correction
  deletions fail for swapping and non-local CNOT in both message orders;
  every high-severity counterexample reproduced and shown fixed.
- PR #18 review (`1a5805f`): all 165 tests and 11 subtests pass; 80 additional
  forward-execution vs. backward-WP exact-matrix comparisons agree; no concrete
  false-`VERIFIED` path found. This is a review result, not a proof that the
  checker is correct.

## Scope and trusted base

- Finite engine: finite classical domains, at most six fixed qubits, user-supplied
  invariants and ranking functions. `INCOMPLETE` never counts as success.
- Unbounded arrays are supported only through the BBPSSW retry-controller
  adapter. Its first-acceptance specifications concern the accepted mass, not
  termination on every resource state; Werner probability/fidelity bounds add an
  i.i.d. Werner-pair assumption and a trusted `q^n -> 0` lemma.
- No Rocq certificate is produced. Python, this implementation, SymPy and Z3 are
  trusted. Results must not be described as machine-checked in the Rocq sense.

## Open follow-ups

- Pin CI dependency versions.
- Add a protocol written by someone else through the public DSL, with faulty
  variants, to test reuse beyond the bundled examples.

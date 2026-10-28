# VeriLocQ

Automated Hoare-logic verification of LOCC protocols, based on LocQHL.
The source and saved Notebook are versioned in `tools/verilocq/`; local environments, runtime files and build outputs are ignored.

[Quickstart.ipynb](Quickstart.ipynb) defines the protocols and checks their Hoare triples.
Every protocol is defined in full in its Notebook cell, followed by explicit specifications and verification calls.
The Notebook includes saved outputs and uses plain text reports throughout. Z3 is an internal backend dependency.

## Hoare triples

```python
from verilocq import program, verify

rsp = program("""
program RSP {
  process Alice {
    qubit A;
    phase alpha;
    bit m;
    bool d;
    R(alpha)[A]; H[A]; m := M[A]; d := false;
    do [] send: not d; c!m -> d := true; od
  }
  ||
  process Bob {
    qubit B;
    bit r,p;
    p := 0;
    do [] receive: p=0; c?r ->
      if r=1 then Z[B]; fi;
      p := 1;
    od
  }
}
""")

result = verify(
    "{ true ; Bell[A,B] }",
    rsp,
    "{ true ; Equator(alpha)[B] }",
    invariant="{ d <=> p=1 ; Z[B]^((1-p)*m) * Equator(alpha)[B] }",
    decreases="1-[d]",
)
print(result)
```

Protocols use `:=`, `H[q]`, `CNOT[a,b]`, `m := M[q]`, `if ... then ... else ... fi`,
and `do [] guard; channel!value -> body [] guard; channel?target -> body od`.
`||` joins processes. Declarations express ownership and types directly:
`qubits A1,A2;`, `bit m1,m2;`, `bool sent;`, and `int x in -1..2;`.
`reference R;` declares an immutable specification qubit.

The argument order is `verify(precondition, program, postcondition)`.
Braced assertions have the form `"{ classical ; quantum }"`; `assertion(classical, quantum)` is also supported.
Results display that triple, its status and the rule/premise summary.
Expand a report to inspect the backward predicate calculations, intermediate W predicates,
measurement-outcome sums, and solver conditions. `result.explain()` opens the same steps all at once;
the Notebook mentions it in a comment rather than displaying a duplicate report.
`result.explain(matrices=True)` also shows recorded precondition/WP/residual matrices;
the displayed valuation is an illustration of the exhaustive case check, not its entire evidence.
`result.details()` retains the plain obligation listing.
Use `and`, `or`, `not`,
`=>` and `<=>` for logic, `=` for equality and `[condition]` for a Boolean indicator.
Quantum predicates include `I`, `Bell[a,b]`, `Zero[q]`, `Plus[q]`, and `Equator(alpha)[q]`.
`phase alpha;` declares a read-only angle. `R(alpha)[q]` applies `diag(1, exp(i*alpha))`,
and `Equator(alpha)[q]` is the projector onto `(ket(0)+exp(i*alpha)*ket(1))/sqrt(2)`.
These are symbolic in every real angle, with a formal unit phase and no sampling.
An inline `gate U { 0: ...; 1: ...; }` definition supplies an exact one-qubit unitary family.
`U(s)[q]` selects a case using a finite classical integer; cases accept rational literals and square roots, not floats.
`Bell[R,A1] * Bell[A2,B]` combines disjoint predicates; `U[q] * A` applies the unitary to a predicate,
and `X[B]^((1-pB)*m2)` denotes a classically controlled Pauli correction.

For guarded protocols, pass an invariant and a ranking function for total correctness.
The Notebook begins with RSP, followed by a fully written RSP program with a missing Z correction.
The failure is explained by the `m=1` measurement outcome, not by a timeout or an artificial enumeration limit.
The order is RSP, teleportation, entanglement swapping, non-local CNOT, distillation, then PhaseChoice.
All programs are defined inline; no imported example factory supplies them.
An edit creates a new definition with `program(old.source.replace(...))`, or by rerunning an edited source cell.

The unbounded example uses the same three-argument `verify` interface, with
`E_pass(0,n)` or `E_good(0,n)` in the precondition and the corresponding paper postcondition.
It generates indexed tensor proofs for the supported first-acceptance definitions. Unsupported quantum specifications are rejected;
the requested classical postcondition is proved from acceptance rather than discarded.

## Case studies

- RSP: one-bit remote preparation of an arbitrary equatorial state, symbolically for every angle.
- PhaseChoice: the scheduler selects between two exact rotations, and the postcondition follows its recorded choice.
- Teleportation: both message orders implement the identity channel on arbitrary inputs.
- Entanglement swapping: both orders establish the remote Bell pair.
- Non-local CNOT: both orders implement the correct two-qubit channel, including entangled inputs.
- Unbounded BBPSSW distillation: indexed tensor derivations and a checked retry-controller adapter establish the two first-acceptance effect specifications for every finite proof horizon `n`, without truncating retries. Separate Werner/i.i.d. assumptions give acceptance and Bell-overlap bounds.

The five fixed-register protocols use the same distributed verifier; RSP additionally uses universal unit-phase algebra.
Distillation uses the indexed proof kernel and retry-controller adapter described below. None produces a Rocq certificate.

## Running

Run these commands from `tools/verilocq/`. Create the environment first using the setup commands below.

```sh
.venv/bin/python -m verilocq --case all
.venv/bin/python -m verilocq --case rsp
.venv/bin/python -m verilocq --case phase-choice
.venv/bin/python -m verilocq --case rsp --omit Z
.venv/bin/python -m verilocq --case teleportation --audit-orders
.venv/bin/python -m verilocq --case swapping --omit Z
.venv/bin/python -m verilocq --case distillation --omit-bilateral-gate Alice
.venv/bin/python -m verilocq --case all --json
.venv/bin/python -m unittest discover -s tests -v
.venv/bin/python scripts/execute_notebook.py
```

Broken examples return exit code 1. `--json --audit-orders` emits one JSON document.
Notebook runtime files stay in `.runtime/`; the script does not register a global kernel.

For a new environment:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[notebook]'
```

`requirements-lock.txt` records the exact dependency versions used for verification.

## Input and results

The main interface is `program` and Hoare-ordered `verify`; `assertion` constructs reusable assertion pairs.
The earlier keyword spelling and `first_acceptance` helper remain available for compatibility.
The source parser lowers these definitions to internal typed command objects, solver expressions,
and exact quantum effects. Parsing does not evaluate Python code. Every compiled effect is checked to satisfy `0 <= A <= I`.
The older `Program` / `Process` / `Branch` constructors remain available for backend tests and advanced integrations.

- `PASSED`: the proof condition has been checked successfully.
- `FAILED`: the proof condition has a counterexample. An unsuitable invariant can cause this; it does not by itself establish that the final program specification is false.
- `INCOMPLETE`: a budget was exceeded or an exact decision could not be made. This never counts as success.
- `VERIFIED`: every required condition passed.
- `NOT_VERIFIED`: at least one condition failed or could not be completed.

Malformed or explicitly unsupported inputs raise `Unsupported`.

## Finite-fragment method

The program itself is our typed Python AST: `Assign`, `Gate`, `Measure`, `If`, `Process`, and so on.
Only classical expressions and conditions are Z3 expressions. Quantum predicates are exact SymPy
matrices selected by finite classical cases, with declared symbolic unit phases when applicable.
There is no translation of an entire quantum program into one Z3 theorem.

For a loop-free block, construct an executable backward weakest-precondition tree:

- Assign: substitute the expression into the classical state used by the remaining predicate.
- Unitary: `W = U† Q U`.
- Meas: `W = sum_m M_m† Q(sigma[x <- m]) M_m`.
- Init: use the reset channel's two Kraus pullbacks.
- If: choose the branch predicate according to the input classical condition.
- Seq: compose these transformers in reverse command order.

The tree used to render the explanation is the one evaluated by the verification check.
An independent forward Kraus interpreter remains for channel audits, distillation's single-attempt
calculation, and cross-checking the WP implementation. The two calculations satisfy:

`wp(L, post)(sigma) = sum_r K_r† post(sigma_r) K_r`.

An assertion's matrix is zero when its classical condition is false. The tool checks `pre <= wp` for every relevant classical input. Measurement paths are not normalized, so probability weights are retained.

Z3 exhaustively enumerates relevant finite classical values and proves classical implications.
It does not prove the quantum operator inequalities: exact Hermitian Schur complements check
`wp - pre >= 0`. Variables are projected out only when backward data dependence shows that they
cannot influence the check. No numerical eigenvalue tolerance can cause acceptance.
Calculation budgets include a WP depth/nesting limit of 256; exceeding it yields `INCOMPLETE`,
not an unhandled Python recursion failure. Report case counts count completed operator comparisons,
not inputs for which the WP calculation itself was cut short.

The distributed verifier generates the paper's initialization, matching communication and invariant-preservation obligations, then checks the exit postcondition. An optional nonnegative integer ranking function adds strict decrease and absence-of-deadlock obligations for total correctness. Without it, the result covers partial correctness only.

The trace identifies the `Distributed`/`Distributed-tot` premises and the exit `Conseq` check.
Local labels such as `Unitary`, `Meas`, `Assign`, `If`, `Seq`, and `Branch-Accum` identify the paper
counterparts of the semantic transformations. The trace does not claim a serialized syntactic
derivation: fresh-outcome handling and accumulation are implemented as the displayed semantic sum.
In particular, intermediate W predicates are operator-valued assertions, not physical execution states.

Classical variables and quantum registers have disjoint process ownership. Classical communication is synchronous. Reference qubits used by Choi specifications are read-only. Each matching pair is checked in one canonical process order, using the paper's independent-step commutation argument.

Supplemental order checks execute both complete message orders for the finite examples. The teleportation channel audit also enumerates all relevant initial classical values; it never silently fixes a relevant scratch bit.

## The retry loop and its array index

Distillation is a guarded loop. `kA`/`kB` are attempt counters: `a_c[kA]` names the current control qubit,
and `a_t[kA]` its target qubit. A rejection increments the counters and consumes fresh cells;
acceptance sets completion flags so the guards become false. Array indexing identifies fresh quantum data and does not impose a loop bound.

The diagnostic `trace_retry(distill, [(0,1),(1,1)])` follows the actual controller through
one rejection and one success, displaying the counters, exchanges and stored measurement records.
This follows specified outcomes rather than simulating quantum probabilities, and it is not the proof.

## Indexed quantum proofs

`verilocq/indexed.py` represents local effects at symbolic indices, identity/zero intervals,
tensor products, finite sums/products, family definitions and local Kraus pullbacks as typed terms.
Tensor factors must occupy adjacent disjoint intervals. Sum binders are scoped and index
substitution avoids capture. Integer side conditions are discharged by SMT.

The proof generator and replay checker are separate. Equality proof objects use `Definition`,
`Sum-Empty`, `Sum-Head`, `Product-Empty`, `Product-Head`, `Sum-Factor`, `Identity-Split`,
`Tensor-Linearity`, `Frame`, `Branch-Accum`, congruence and transitivity. The checker validates
every rule's endpoints and side conditions. Local equalities use exact matrix coefficients.
There is no BBPSSW, Bell-state or first-acceptance axiom in the kernel.

The current generator recognizes the first-hit finite-sum form and derives its recurrence from
that definition. Interval induction proves `0 <= E(k,n) <= I`: the empty interval is zero;
the step uses the strictly smaller suffix and checks both positivity decompositions.
The checker grants the suffix hypothesis only inside that induction step. It does not enumerate `n`.

`Frame` lifts each actual local Kraus pullback to an arbitrary suffix. `Branch-Accum` sums
the branches and the derived recurrence identifies the result with the indexed precondition.
This is an operator proof on the whole register interval, including correlated inputs;
no global `4n`-qubit matrix or product-input assumption is needed.

The kernel works with other local dimensions and exact effects. Tests include a two-dimensional
repeat-until-success instrument and nonprojective effects, independent of the distillation adapter.
The Python kernel, tensor/positivity/induction rules, exact matrix engine and SMT solver remain
trusted implementation components; these proof objects are not Rocq certificates.

## Unbounded distillation controller

`verilocq/distillation.py` connects the actual two-party retry controller and circuit to indexed proofs. Counter variables range over unbounded natural numbers; `n >= 1` is a logical proof parameter.

The backend checks:

- The exact four-qubit acceptance, rejection, target-Bell and trace-preservation Kraus identities.
- Initialization and every communication body's classical invariant, with symbolic counters.
- Every feasible command path either leaves the tested quantum selector unchanged or tests both parties' fresh cells at index `k+1`. Initialization must test index zero.
- The paper's nonnegative rank, strict decrease, and no-deadlock condition.
- Replayed finite-sum recurrences, framed measurement pullbacks, and effect-bound induction for both first-acceptance predicates.

The generated tensor step is `E_pass(r,n) = Pass_r tensor I_tail + Rej_r tensor E_pass(r+1,n)`; `E_good` uses `Good_r` for the head. It is derived from the finite sum by checked sum splitting, product splitting, factoring and definition folding. The bounds and circuit pullback are separate replayed proofs.

This establishes first-acceptance precondition mass, not termination for every possible resource state. Inputs outside that mass may retry forever. The additional geometric probability and fidelity formulas assume independent Werner resource pairs. Finite `n` bounds are lower bounds on accepted output mass and Bell overlap; `g/p` is the asymptotic fidelity under that product-input assumption.

## Paper-rule Hoare proofs

The executable loop, fresh arrays and the two first-acceptance specifications agree with the paper.
The generated distributed proof uses the paper's invariant `theta and kA<n` and its bound function.
The frontend spelling `theta` with `K=0` outside the proof horizon denotes the same quantitative assertion.

`verilocq/hoare.py` constructs and replays the local and distributed judgments. `Assign` substitutes
into both assertion parts; `Unitary` constructs the source gate's predicate pullback; `Meas` introduces
a fresh typed logical outcome and records its equality with the measurement variable. `Aux-Subst`
instantiates that outcome, and `Branch-Accum` checks outcome exclusion and predicate bounds before
accumulating. `Seq`, `If`, `Assert-Eq`, and `Conseq` check their actual intermediate assertions.

`Distributed-tot` requires initialization, invariant preservation for every actual matching pair,
and a ranking triple for every pair with a fresh logical integer. It also checks nonnegative rank,
absence of deadlock, and the exact invariant/TERM conclusion. A final `Conseq` establishes the
requested postcondition. An omitted, duplicated, unrelated or malformed proof cannot establish verification.

Quantum consequence conditions are checked by exact local operator algebra on symbolic register
intervals, with the replayed indexed recurrences. The operator basis retains the identity explicitly,
so measuring unused registers does not require constructing a global matrix. Classical conditions
are checked by SMT with declared symbol types. Cache keys retain typed Z3 ASTs rather than relying
on their printed text; local definitions may not change during proof replay.

The source-language adapter still supports this retry layout and its K predicates; it does not
discover arbitrary invariants or support every indexed source program. The proof rule engine and
the indexed algebra kernel are Python implementations, not Rocq certificates. The finite-register
examples retain their existing semantic-WP backend.
The `E_pass`, `E_good`, `K_pass`, and `K_good` source forms dispatch to the indexed generator and retry-controller adapter;
they are not arbitrary Z3 predicates. The indexed term/proof API is available in `verilocq.indexed`;
the public protocol parser has not been extended with arbitrary family declarations.
Expand the report's paper-rule obligations to see the Hoare proof trees and intermediate W predicates.
The local Pass/Rej/Good identities and indexed tensor derivations are also retained as inspectable evidence.

## Probability and fidelity bounds

These are required verified consequences of the distillation example. After successful verification,
`distill_good.bounds(fidelity="4/5", attempts=5)` returns the general theorem and its exact instance.
The evidence includes one-attempt Werner traces, the zero-horizon base case, both geometric recurrences,
probability-range induction, `0<1-p<1`, and `g/p>F`. The limiting step applies the explicitly identified
trusted real-analysis lemma `q^n -> 0` for `0<q<1`; it is not a numerical limit experiment.
Failed or incomplete triples cannot export a verified bound.

## Scope and trust

The finite engine supports finite Boolean/integer domains, at most six total fixed qubits including references, H/X/Z/CNOT, read-only symbolic phase rotations R(alpha), exact finite one-qubit gate families,
computational-basis measurement, reset, local sequential/conditional blocks, and guarded synchronous classical communication. A value escaping its declared finite domain causes an incomplete check rather than wrapping or truncation.

Read-only angle parameters are interpreted as formal unit phases with conjugate(z)=1/z. Exact Hermitian Schur complements
can prove suitable phase-dependent inequalities; undecidable signs never count as successful proofs.
This is not arbitrary real-valued classical computation: phase parameters cannot be assigned or used in classical guards.

The protocol frontend handles unbounded arrays only through the distillation controller adapter. General continuously parameterized gate families beyond the
supported phase algebra, general symbolic matrix inequalities, invariant synthesis, arbitrary Python verification and Rocq certificates remain outside the scope.

The trusted base includes this Python implementation, SymPy, Z3 and Python itself. Exact calculations do not mean the implementation has been formally certified.

## Source files

- `verilocq/syntax.py`: input language, typing, ownership and data dependencies.
- `verilocq/frontend.py`: paper-style source parser, cq-assertion notation, and public verification API.
- `verilocq/quantum.py`: exact effects, tensor embedding and positivity.
- `verilocq/indexed.py`: indexed operator terms, proof generation and rule replay.
- `verilocq/hoare.py`: paper-rule Hoare trees, typed consequence checking and Distributed-tot replay.
- `verilocq/verifier.py`: local weakest preconditions, distributed checks and plain reports.
- `verilocq/derivation.py`: executable WP trees, recorded operator evidence, and expandable derivation views.
- `verilocq/examples.py`: internal regression examples and supplemental order audits; Notebook definitions do not call these factories.
- `verilocq/distillation.py`: unbounded controller checks and indexed-proof integration.
- `verilocq/pretty.py`: readable rendering of actual program objects.
- `tests/`: positive cases, deliberate mutations, input validation and review regressions.
- `scripts/build_notebook.py`: regenerate the English walkthrough and clear old outputs.
- `scripts/execute_notebook.py`: execute it and save outputs.
- `REVIEW.md`: independent review findings and their resolution.

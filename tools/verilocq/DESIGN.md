# VeriLocQ design notes

How VeriLocQ generates and decides proof obligations. Usage is described in [README.md](README.md).

## Frontend

The main interface is `program` and Hoare-ordered `verify`; `assertion` constructs reusable assertion pairs.
The earlier keyword spelling and `first_acceptance` helper remain available for compatibility.
The source parser lowers these definitions to internal typed command objects, solver expressions,
and exact quantum effects. Parsing does not evaluate Python code. Every compiled effect is checked to satisfy `0 <= A <= I`.
The older `Program` / `Process` / `Branch` constructors remain available for backend tests and advanced integrations.

The unbounded example uses the same three-argument `verify` interface, with
`E_pass(0,n)` or `E_good(0,n)` in the precondition and the corresponding paper postcondition.
It generates indexed tensor proofs for the supported first-acceptance definitions. Unsupported quantum specifications are rejected;
the requested classical postcondition is proved from acceptance rather than discarded.

## Case-study backends

The five fixed-register protocols use the same distributed verifier; RSP additionally uses universal unit-phase algebra.
Distillation uses the indexed proof kernel and retry-controller adapter described below. None produces a Rocq certificate.

## Finite-fragment method

The program itself is our typed Python AST: `Assign`, `Gate`, `Measure`, `If`, `Process`, and so on.
Only classical expressions and conditions are Z3 expressions. Quantum predicates are exact SymPy
matrices selected by finite classical cases, with declared symbolic unit phases when applicable.
Declared normalized state parameters also remain symbolic.
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
It does not prove the quantum operator inequalities: exact Hermitian projector identities and Schur complements check
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

### Arbitrary normalized input states

`state psi;` declares a specification parameter corresponding to the Rocq hypotheses `psi : Vector 2`, `WF_Matrix psi` and `psi† * psi = I 1`.
The predicate `rho(psi)[q]` denotes `psi * psi†` on register `q` and identity on other registers.
The parameter is not a qubit, cannot be assigned or used in classical guards, and is retained in the typed program representation for a future Rocq exporter.

Internally, `psi` is represented, up to global phase, by `cos(theta)|0> + z*sin(theta)|1>`, with an arbitrary real `theta` and a formal unit phase `z` satisfying `conjugate(z)=1/z`.
This representation covers every normalized one-qubit projector, including both computational-basis states, without dividing by either amplitude.
The angle and phase stay symbolic throughout successful verification.
Exact Hermitian idempotence, `P†=P` and `P*P=P`, supplies a positivity certificate when a symbolic projector cannot be handled by a strictly positive Schur pivot.
Effects with state parameters must also have finite entries for every parameter value.

If a symbolic inequality cannot be decided, exact instantiated states may provide a counterexample.
Passing any number of such instances never establishes verification, and an undecided inequality remains `INCOMPLETE` if no counterexample is found.
Teleportation uses the same three-qubit `rho_psi tensor Bell` to `I tensor I tensor rho_psi` specification as `CaseStudies/Teleportation.v`.
`state psi[2];` declares an arbitrary normalized joint vector on two qubits, corresponding to `psi : Vector 4` with the same well-formedness and normalization hypotheses.
Its four complex amplitudes stay symbolic, with `sum_i a_i*conjugate(a_i)=1` as the only relation.
Polynomial equalities are reduced modulo this normalization equation by exact Groebner reduction, without assuming any amplitude is nonzero or that the two qubits are separable.
Non-local CNOT uses four protocol qubits and the current paper's `Bell[A,B] * rho(psi)[C,T]` to `CNOT[C,T] * rho(psi)[C,T]` specification.
This follows the current paper rather than the older Choi-style specification in `CaseStudies/NonlocalCNOT.v`.

### Correspondence with the current paper

The case-study programs, specifications, invariant formulas and ranking functions were checked against the current `LOCQHL_PLDI27` sources.
Omitted `else skip` branches, explicit `skip` commands, ASCII register names and bit-domain conjuncts already supplied by declarations do not change the programs or assertions.

| Case | Paper source | Input and target | Ranking function |
|---|---|---|---|
| Teleportation | `example.tex`, `CSTele` and Appendix B.1 | arbitrary `psi[A1]` with Bell resource to `psi[B]` | `2-[dAz]-[dAx]` |
| Entanglement swapping | `example.tex`, `CSSwap` and Appendix B.2 | two initial Bell pairs to `Bell[A,B]` | `2-[dCA]-[dCB]` |
| Distillation | `example.tex`, `CSDistill` and Appendix B.3 | both first-acceptance effects to acceptance or acceptance with the retained Bell pair | `2*(n-kA)-[sentA]-[recvA]` |
| Non-local CNOT | Appendix C.1 and `CSRCNOT` | arbitrary joint `psi[C,T]` with Bell resource to `CNOT[C,T]*psi[C,T]` | `2-[dA]-[dB]` |
| Remote state preparation | Appendix C.2 and `CSRSP` | Bell resource to the equatorial state, with `0<=alpha<2*pi` preserved | `1-[d]` |
| PhaseChoice | Appendix C.3 and `CSPhase` | Bell resource to `U(s)[B]*Bell[A,B]`, with the paper's exact `9/10` and `7/10` cases | `1-[a]` |

Read-only phase-domain assertions are retained in the public specifications.
Their Boolean domain consequences are checked by SMT under `0<=alpha<2*pi` and the positivity of pi before finite classical verification.
The quantum backend checks every unit phase, covering the whole declared angle domain.
It rejects narrower angle-dependent restrictions, which cannot be justified by treating the real angle and its unit-phase symbol independently.

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
The Notebook explicitly writes `theta and kA<n`, matching the paper.
For the classical controller audit, the frontend removes only that explicit horizon conjunct because `K=0` outside the horizon makes the two quantitative assertions equal.
The replayed Hoare proof retains `theta and kA<n` at its invariant checkpoints.

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

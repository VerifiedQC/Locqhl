# VeriLocQ independent implementation review

This is a chronological review log. The initial section covers the backends
through version 0.2; the versioned follow-ups below record subsequent independent
reviews through VeriLocQ 0.8.0. Historical limitations and test counts describe
their stated versions, not the current version. The initial v0.3 source-interface
update had author-only validation with 66 passing tests and a successfully
executed Notebook; later sections distinguish the subsequent independent checks.

Reviewed by a separate agent at the user's request. The reviewer inspected the
implementation, compared the proof obligations with `rules.tex` and the
expectation semantics in `corr-spec.tex`, and ran independent checks. The
reviewer did not modify the implementation; the implementation author fixed the
findings below. This file records the review and follow-up verification.
The original review is followed by versioned follow-ups below, which record
the later independent reviews and distinguish historical implementation
boundaries from the current ones.

The current code is a useful research prototype with a reasonably clear
separation between syntax, exact quantum algebra, proof obligations, examples,
and presentation. The finite verifier computes actual Kraus-map pullbacks and
checks operator inequalities; its successful example results are not preset.
The additional distillation backend implements a specialized proof schema.
After the fixes described below, this review found no remaining concrete path
to a false `VERIFIED` result through the reviewed verification entry points.
This is a review conclusion, not a proof that the implementation has no bugs.

## Findings and resolutions

- **High severity: measurement records could be corrupted without invalidating
  the distillation proof.** Adding `mA := 1 - mA` after every Alice measurement
  in the initialization and retry bodies originally left the schema result
  `VERIFIED`. The controller then accepted different physical outcomes, while
  the matrix proof still described the original acceptance condition. The
  symbolic trace originally checked the measurement command shape but did not
  bind the final classical record to the recorded physical outcome. The fix
  records the exact outcome of each measurement and checks that the fresh test's
  output records still equal those outcomes. The independent reproduction now
  produces `NOT_VERIFIED`, and a regression covers it.

- **High severity: the proof horizon could become mutable executable state.**
  Giving `n` to Alice and prepending `n := 1` originally passed the schema even
  though the specifications require an immutable external proof parameter.
  The fix enforces the complete ownership map, prohibits executable access to
  `n`, and checks preservation of `n` on symbolic paths. The reproduction is now
  rejected as unsupported, with a regression.

- **High severity, found by the implementation author's final self-review:
  weakening the supplied invariant could hide incorrect acceptance.** Removing
  the implication from completion to equal outcomes and making both parties
  accept unconditionally after receiving both messages bypassed the intended
  quantum-selector reasoning. A check of the classical acceptance flags alone
  was insufficient for the first-acceptance quantum specifications. The fix
  requires the supplied invariant to imply the canonical invariant's selector
  facts and separately checks that termination below the horizon implies equal
  outcomes. The independent reviewer reconstructed this mutation after the fix:
  both added obligations failed and the induction conclusion was marked
  `INCOMPLETE`. The targeted regression passes, and the correct schema still
  passes.

- **Medium severity: a public implication check accepted malformed programs.**
  Two declarations of the same variable with conflicting singleton domains
  made the domain assumptions inconsistent. The exported `check_implication`
  could therefore report that `True` implied `False`, although ordinary program
  validation rejected those declarations. The public function now validates
  the program before proving an implication. A regression rejects this input.

- **Medium severity: the supplemental teleportation channel audit silently fixed
  scratch inputs.** A conditional input correction based on the initial value
  of `m1` was detected by the general verifier, but the channel audit initially
  inspected only the default initial value. The audit now enumerates relevant
  initial classical dependencies and reports their values. The mutation is
  covered by a regression; it no longer receives a uniformly successful audit.

- **Medium severity: failed distillation programs could still export successful
  probability bounds.** `bounds()` originally returned the reference protocol's
  formulas for a protocol with an omitted bilateral CNOT. It now requires a
  successful verification of the current protocol before exporting its bounds.
  The failing-program regression passes; valid exact Werner bounds remain
  available.

- **Low severity: the specialized schema ignored changed layout declarations.**
  Its structural interpretation assumed a specific array-template layout.
  Validation now requires that exact layout and rejects reference registers.
  A changed-layout regression passes.

- **Low severity: combined JSON and audit output was not valid JSON.** The CLI
  originally appended Python dictionary representations after its JSON result.
  It now emits one JSON document for the combined options. The corresponding
  parsing regression passes.

## Validation performed

- Independently ran the original 27-test suite successfully.
- Compared the exact positive-semidefinite checker against the independent
  all-principal-minor criterion on 300 generated rational Hermitian matrices
  of dimensions two, three, and four. All decisions agreed.
- Independently ran the expanded 40-test suite successfully before the final
  two regressions were added.
- Reproduced both high-severity distillation failures and verified their fixes.
- Checked the swapping and non-local CNOT implementations and both complete
  communication orders. The correct programs passed; deleting either required
  Pauli correction failed both the invariant checks and the supplemental order
  checks.
- Independently ran the final targeted tests for failed-protocol bounds,
  changed schema layouts, and valid exact Werner bounds. All three passed.
- Independently ran the added weakened-invariant/incorrect-acceptance regression
  and the correct parametric-schema test after the author's final self-review
  fix. Both passed. The suite at that review snapshot contained **43 tests**.

The implementation author runs the final complete suite separately. This
review distinguishes those author-run checks from the independent executions
listed above.

## Scope and remaining trust assumptions

The finite verifier's conclusion applies to its declared finite classical
domains, fixed register sets, supported primitive operations, and supplied
invariant. Exact matrix calculations avoid floating-point acceptance
thresholds. Exhausting an exploration budget or failing to decide a sign must
produce `INCOMPLETE`; a failed intermediate proof obligation does not by itself
show that the user's overall specification is false.

The unbounded distillation backend is a specialized, trusted Python proof rule
for the checked BBPSSW control and fresh-resource structure. It combines exact
four-qubit acceptance/rejection/Bell-output identities with unbounded symbolic
counter checks, indexed-event checks, and a tensor induction over the finite
proof horizon. It does not truncate the retry loop. The tensor argument relies
on disjoint fresh register support; the first-acceptance effect specifications
do not require an independent quantum input across attempts. The reported
Werner probability and fidelity formulas separately require the stated
independent, identically prepared Werner-pair assumption.

This backend is not a general verifier for arbitrary programs with unbounded
quantum arrays, and it does not discover arbitrary induction principles or
invariants. Its first-acceptance specifications concern the mass represented
by those effects, not termination on every possible resource state.

There is no Rocq proof certificate, and neither the VC generator nor the tensor
induction implementation has been formally verified. Python, the implementation,
SymPy, Z3, and the mathematical soundness of the implemented proof rules remain
part of the trusted basis. Those boundaries should remain visible whenever the
tool's results are described in the paper or an artifact submission.

## v0.4 follow-up: RSP, PhaseChoice, and control traces

On October 28, 2026, the independent reviewer inspected the new source-level
RSP and PhaseChoice support, symbolic phase algebra, finite gate families, and
retry-control illustration. This was a targeted follow-up rather than a
restart of the original review. No new false `VERIFIED` result was found in the
reviewed extensions.

- The unit-phase symbol uses conjugation as inversion without assuming the
  phase is real or positive. The reviewer checked those assumptions and the
  equatorial projector's exact positivity. RSP keeps the declared phase
  symbolic, so its conclusion concerns every permitted angle rather than
  numerical samples. Undeclared free symbols remain disallowed in effects.
- Phase inputs are immutable and owned by their declaring process. Independent
  checks rejected assignment to a phase input, a different process reading
  that input, and a gate family reading another process's classical selector.
- Finite gate-family cases are checked as exact unitaries. Independent tests
  confirmed that gate selectors participate in classical input dependencies:
  a selector-dependent identity/X gate cannot incorrectly pass an unconditional
  zero-state preservation claim.
- Generic integer gate powers are no longer reduced modulo two. An independent
  order-four gate example passed when executed twice against the squared-gate
  target, while an unchanged input failed against that target.
- The revised Hermitian test compares a simplified matrix difference. The
  targeted exact complex-algebraic projector regression passed. PhaseChoice
  passed for its recorded-choice specification; a single fixed output could
  not stand in for both scheduler choices.

The reviewer independently ran all 21 initial tests in
`test_additional_protocols.py`, as well as the complete source-defined Notebook
execution test. Those checks passed. Additional ad hoc selector, ownership,
and gate-power checks also passed. The implementation author runs the final
expanded suite separately. The implementation author reports that all **90
tests passed** and the RSP-first Notebook executed all **13 code cells**
successfully. The author also reports that `--case all --audit-orders` includes
RSP and PhaseChoice alongside the original four examples. This follow-up does
not claim an independent rerun of that entire expanded suite or CLI run.

One **low-severity presentation finding** concerned the retry illustration.
After adding classical postprocessing `mA := 1-mA`, the trace originally
described the stored bit as the physical measurement outcome. The controller's
execution was followed correctly, but the explanation conflated two different
values. The fix separately prints the specified physical outcomes and stored
records, describes communication as exchanging the recorded bit, and labels
the comparison as agreement or disagreement of recorded bits. The reviewer
independently ran the exact postprocessing-mutation regression after the fix;
it passed.

The retry trace remains a control-flow illustration for supplied outcomes,
not a quantum simulation, probability calculation, or proof. The symbolic
phase operations and exact gate-family checks extend the trusted Python
implementation; they do not add a Rocq certificate or formally verify the
implementation. The earlier finite-fragment and specialized distillation-schema
boundaries remain in force.

## v0.5 follow-up: Hoare-ordered verification and derived bounds

The independent reviewer inspected the interface that accepts
`verify("{ phi ; A }", protocol, "{ psi ; B }", ...)`, its concise triple report,
and its unbounded-specification and probability-bound paths. The reviewer ran
the initial 16 Hoare-interface tests successfully and performed additional
checks of strengthened classical preconditions, non-Boolean requested goals,
and a false requested postcondition attempting to export bounds. No concrete
false-goal verification or unchecked-bounds path was found.

For unbounded programs, the interface restricts the quantum precondition,
invariant family, and target to the supported corresponding first-acceptance
specifications. The requested classical postcondition is separately checked
as a consequence of acceptance; it is not discarded. Scalar probability
evidence includes the zero-horizon base, recurrence identities, range
preservation, and the hypothesis needed for geometric decay. Failed requested
triples cannot export successful protocol bounds, and exporting bounds also
rechecks the current protocol through the underlying retry proof.

One **low-severity compatibility finding** was the rejection of the previously
valid fully keyword-based call `verify(protocol=p, pre=..., post=...)`.
The implementation now routes that form explicitly while retaining positional
Hoare order and rejecting mixed argument styles. The reviewer independently
ran the new compatibility regression successfully. The reviewer also confirmed
the targeted split-identifier regression: unbounded quantum specifications
are compared using parsed AST structure, so whitespace cannot silently turn a
malformed identifier into a recognized effect. These two targeted regressions
passed after the fixes.

Separately from those independent targeted checks, the implementation author
reports that the complete **109-test suite passed** and the final Notebook
executed all **17 code cells**, saving their outputs. The author also confirmed
English-only, table-free output and the top-level order RSP, teleportation,
swapping, non-local CNOT, distillation, and PhaseChoice, with probability bounds
included as required verified results. The independent reviewer did not rerun
that entire final suite or Notebook during this targeted follow-up.

The three-line display is a presentation layer; `details()` retains the full
proof obligations. The trusted-implementation boundary is unchanged. The
fresh-factor tensor induction and the explicitly labeled geometric-limit rule
are trusted mathematical rules implemented in Python, not Rocq-checked
certificates. The latter applies the standard limit for a rejection factor
strictly between zero and one after checking that hypothesis; it does not
estimate a limit by sampling.

## v0.6 follow-up: executable WP evidence and proof explanations

The independent reviewer inspected the executable backward-predicate tree now
used by the local verification kernel. Assignment updates the classical state,
unitaries pull predicates back by conjugation, measurements sum outcome
pullbacks with updated classical records, reset sums its two Kraus pullbacks,
and conditionals select the appropriate branch. The independent forward
Kraus interpreter remains available for comparison. All 11 initial derivation
tests passed independently, including agreement between the two calculations
on 12 classical inputs with parameterized gates, entanglement, measurements,
reset, conditionals, and assignments. No false verification result was found.

The review identified two issues, both fixed:

- **Medium severity, robustness:** a 1,200-command sequential block exhausted
  Python's recursion limit. WP evaluation and nested construction now enforce
  an explicit safe depth budget of 256, producing `INCOMPLETE` when exceeded.
  Rule collection and explanation traversal are iterative, so the incomplete
  long-chain report can still be rendered.
- **Low severity, evidence accuracy:** interrupted evaluations counted attempted
  inputs as completed operator checks, and sample wording implied full
  coverage even for incomplete obligations. Counts now advance only after
  computing the operator comparison, agree with the recorded local evidence,
  and distinguish incomplete coverage and vacuous zero-case checks.

The reviewer independently ran five targeted regressions after these fixes:
long sequential blocks, deeply nested conditionals, path-budget completion
counts, incomplete matrix-sample wording, and vacuous checks. All five passed.

Separately, the implementation author confirmed that all **124 tests passed**,
including the **15 derivation tests**, and that the Notebook executed and saved
all **18 code cells** with WP formulas and expandable proof evidence. The author
also confirmed English-only, table-free output and explicit labels for trusted
tensor and geometric rules. These full-suite and Notebook results are distinct
from the independent 11-test initial run and five targeted fix checks above.

The displayed tree is the actual semantic WP computation, and recorded matrix
samples come from that computation. Paper rule names identify correspondence;
the trace does not claim a serialized syntactic derivation or a Rocq proof.
The specialized tensor induction and geometric-limit rules remain explicitly
trusted rules, and the earlier implementation and dependency trust boundaries
remain unchanged.

## v0.7 follow-up: indexed proof replay

The independent reviewer inspected the new generic indexed operator/proof
kernel and its distillation integration. Terms carry register intervals;
replayed rules check sum/product transformations, tensor algebra, local Kraus
framing, positivity, and interval induction. The current first-acceptance
generator produces proof objects that are checked separately rather than
being accepted as assertions.

The review found one **high-severity binder-scope error**. Entering a finite sum
retained an ambient assumption about the same symbol used as its binder.
Combining an outer `i=100` assumption with the sum's local `0<=i<2` assumptions
made the context inconsistent and allowed an invalid product-empty step under
congruence. The reviewer constructed an accepted equality whose two dense
interpretations were `diag(2,2,1,1)` and `diag(2,2,2,2)`. The fix requires each
sum binder to be fresh in the surrounding proof context, including when
checking a congruence subproof. The counterexample is now rejected and has a
dedicated regression.

Independent validation passed all 18 initial indexed tests and all 20 updated
indexed tests after the binder fix and resource-budget checks. These include
small independent dense interpretations, entangled-input framing, nonprojective
local effects, capture-avoiding substitution, interval typing, invalid proof
steps, and scoped induction hypotheses. The reviewer also independently passed
both integration regressions rejecting a missing induction proof and an
unrelated but valid equality substituted for the requested pullback proof.
The adapter now binds the exact requested family and constructs the requested
WP independently from the actual source Kraus outcomes; its identity operator
is defined before invoking the proof generator. No additional concrete false
acceptance was found after these fixes.

Separately, the implementation author confirmed that the complete **146-test
suite passed**, including the 20 indexed tests and both proof-goal integration
regressions. That author-run full suite is distinct from the independent
targeted executions above.

The quantum rule checker is protocol-independent, but the current source
lowering and retry-controller adapter remain specialized. Generic quantum
terms do not imply support for every indexed source program or automatic
invariant discovery. The earlier blanket acceptance of a specialized tensor
induction schema has been replaced by replayed finite-sum, frame, and induction
proofs; the Python kernel's algebra, positivity and induction rules remain
trusted implementation components. There is still no Rocq certificate, and
the separate geometric-limit lemma remains explicitly trusted.

Final author validation also executed and saved all **17 Notebook code cells**
without errors, confirmed that the indexed rule steps appear in the saved
outputs, and checked that the Notebook contains no tables, duplicate expanded
RSP report, or removed explanatory labels. After the identity-definition
hardening, all 18 case-study tests passed again.

## v0.8 follow-up: replayed paper-rule Hoare proofs

The project is now named VeriLocQ, with directory and Python package
`verilocq`, version 0.8.0. This follow-up inspected the new paper-rule proof
objects, their replay checker, and the indexed consequence oracle. The replay
checks local Assign, Unitary, Meas, Aux-Subst, Branch-Accum, Seq, If, Assert-Eq
and Conseq applications, as well as the initialization, communication coverage,
ranking and deadlock premises of Distributed-tot.

The independent review found and helped resolve the following issues:

- **High severity, logical-variable shape and freshness:** expression-valued
  measurement outcomes and auxiliary substitution operands were accepted as
  logical variables. Concrete counterexamples produced false local triples;
  one accepted `{true; I} mA:=0 {false; I}`. A constant ranking variable would
  likewise make all decrease premises vacuous for an infinite rendezvous loop.
  The checker now requires genuine fresh zero-arity integer constants, checks
  read/write restrictions, and rejects the constant-ranking construction.
- **High severity, index identity:** a SymPy Dummy named `kA` could alias the
  source counter despite denoting a different symbolic index. This let the
  oracle treat an operation on one array cell as correcting another. Index
  translation now preserves Dummy identity, substitution matches canonical
  symbols exactly, and undeclared or captured free indices are rejected.
- **High severity, memoization identity and rejected-input poisoning:** textual
  cache keys conflated Boolean and integer declarations. An overloaded
  uninterpreted function named `+` also printed like built-in addition, so
  merely including free-variable sorts did not resolve the problem. A rejected
  proof could previously cache a Boolean tautology and cause a later false
  integer consequence to pass. Inputs are now validated before SMT memoization,
  and the final cache key uses live, context-specific Z3 AST identity.
- **Low severity, malformed syntax under vacuity:** an unknown predicate kind
  could bypass checking under a false classical guard. Predicate, operator-term
  and operation constructors now reject unsupported kinds and invalid arities
  independently of reachability.

Additional checks establish predicate bounds, complete instrument sums, Kraus
contraction and explicit tensor boundaries, including identity-only factors.
The checker also guards against changes to the quantum definitions and declared
domains after checking begins. These checks prevent an untyped intermediate
formula from being presented as an application of a paper rule.

The reviewer inspected the final `ASTKey` design independently. Its comparison
and hash use the context identity and live AST identifier; it owns an expression
reference excluded from Python comparison and hashing. That reference keeps
the AST and context alive, preventing identifier reuse while a key remains in
a cache. Z3 AST identity distinguishes sorts, declarations and children, and
Python key comparison does not invoke symbolic Z3 equality. No issue was found
with that final form in this targeted review.

Independent validation was performed at distinct implementation snapshots:

- All 16 initial Hoare-rule tests passed after the substantive soundness fixes.
- An integrated distillation verification passed both paper triples, replaying
  243 Hoare nodes for each of `E_pass` and `E_good`. This smoke run preceded the
  final AST-key performance change.
- All 17 current `test_hoare.py` tests passed after the final key and constructor
  changes, including the cache-poisoning, freshness, index-capture, effect-bound,
  malformed-syntax and constant-ranking regressions.

No remaining concrete false triple was found after those fixes. The consequence
oracle currently proves the equalities needed by the supported derivations;
this does not establish completeness for arbitrary quantum inequalities.
The source/controller adapter remains specialized, even though the indexed
operator rules and Hoare replay machinery are separate. These are executable
Python proof checks, not Rocq certificates or a formal proof of the checker's
own soundness. The algebra engine, SMT solver, Python kernels and separate
geometric-limit lemma remain in the trusted basis.

Final author validation passed the complete **164-test suite**. After adding
an additional entry-point check rejecting invalid program domains, all **18
Hoare-rule regressions** passed. All **15 derivation/display tests** also passed
after numbering proof nodes and adding premise references. These author runs
are separate from the independent executions above.

The renamed Notebook executed and saved all **17 code cells** without errors.
Saved output contains the numbered Hoare trees, premise links and target
definitions, with no tables or duplicate expanded RSP report. Both the RSP CLI
from outside the project directory and the final distillation CLI passed. The
editable package, CLI, virtual-environment entry points and ignore rule use
`verilocq`; no paper TeX source was edited for this implementation.

## Naming update: VeriLocQ

The project directory, Python package, CLI, Notebook, documentation and ignore
rule now consistently use `verilocq` / `VeriLocQ`. The virtual environment and
editable installation were relocated, and the obsolete package entry was
removed. No verification logic was changed. All 18 Hoare-rule tests and 20
indexed-proof tests passed; all 17 Notebook cells executed and saved without
errors. The renamed CLI was also checked from outside the project directory.

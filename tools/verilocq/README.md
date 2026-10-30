# VeriLocQ

VeriLocQ checks LocQHL Hoare triples for distributed LOCC protocols automatically.
Users write the protocol, its pre- and postcondition, and a loop invariant.
VeriLocQ checks that initialization establishes the invariant, each communication preserves it, and the postcondition holds when the protocol finishes.
It uses Z3 for classical conditions, exact matrix calculations with SymPy for finite quantum systems, and symbolic tensor proofs for distillation.
If a check cannot be completed, it reports `INCOMPLETE`.

## Installation

Python 3.11 or later is required.
From `tools/verilocq/`

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[notebook]'
```

`requirements-lock.txt` records the exact dependency versions used for verification.
All commands below are run from `tools/verilocq/`.

## Quick start

Remote state preparation (RSP).
Alice and Bob share a Bell pair.
Alice rotates and measures her half and sends the outcome to Bob, who applies a Z correction when the outcome is 1.
Afterwards Bob holds the equatorial state with phase `alpha`, for every angle `alpha`.

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
    "{ 0 <= alpha and alpha < 2*pi ; Bell[A,B] }",
    rsp,
    "{ 0 <= alpha and alpha < 2*pi ; Equator(alpha)[B] }",
    invariant="{ 0 <= alpha and alpha < 2*pi and (d <=> p=1) ; Z[B]^((1-p)*m) * Equator(alpha)[B] }",
    decreases="1-[d]",
)
print(result)
```

Output

```
For every phase alpha with 0 <= alpha < 2*pi:
{ 0 <= alpha and alpha < 2*pi ; Bell[A,B] }
RSP
{ 0 <= alpha and alpha < 2*pi ; Equator(alpha)[B] }

VERIFIED (total correctness)

Proof: [Distributed-tot]
  [PASSED] Initialization establishes invariant [Seq, Unitary, Meas, Assign]
  [PASSED] Invariant preserved: Alice.send ↔ Bob.receive [Seq, Assign, If, Unitary]
  [PASSED] Exit implies classical postcondition
  [PASSED] Exit implies quantum postcondition [assertion entailment]
  [PASSED] Ranking function is nonnegative
  [PASSED] No deadlock under invariant
  [PASSED] Ranking decreases: Alice.send ↔ Bob.receive
```

Each line is one proof obligation, including the premises of `Distributed-tot` and the final postcondition check.
The brackets list the local rules used to compute it.

## Writing a protocol

A program is a list of processes joined by `||`.

```
program Name {
  state psi;
  gate U { 0: ...; 1: ...; }
  process Alice { declarations  initialization  do ... od }
  ||
  process Bob { ... }
}
```

The `state` and `gate` lines are optional.
Each process declares its own variables and qubits, runs an initialization block, and then an optional communication loop `do ... od`.
Variables and qubits belong to the process that declares them.

### Declarations

| Declaration | Meaning |
|---|---|
| `qubit A;` or `qubits A1, A2;` | qubits owned by the process |
| `bit m;` | classical variable over 0 and 1 |
| `bool d;` | Boolean variable |
| `int x in -1..2;` | integer variable over a finite range of at most 256 values |
| `phase alpha;` | read-only symbolic angle, verified for every real value |
| `state psi;` | program-level parameter for an arbitrary normalized one-qubit state, used only in specifications |
| `state psi[2];` | arbitrary normalized two-qubit joint state, including entangled states |
| `array`, `nat` | used by the distillation controller only |

### Commands

| Command | Meaning |
|---|---|
| `x := e;` | classical assignment |
| `m := M[q];` | computational-basis measurement of `q` into `m` |
| `q := \|0>;` | reset `q` to `\|0⟩` |
| `H[q];` `X[q];` `Z[q];` `CNOT[a,b];` | primitive gates |
| `R(alpha)[q];` | phase rotation `diag(1, exp(i*alpha))` |
| `U(e)[q];` | case `e` of a declared gate family |
| `if c then ... else ... fi` | conditional, `else` is optional |
| `skip;` | no operation |

A gate family lists exact one-qubit unitaries by integer case.
Cases are written with `I`, `X`, `Z`, `H`, `i`, integers, fractions and `sqrt`.
Floats are not accepted.

```
gate U {
  0: sqrt(9/10)*I + i*sqrt(1/10)*Z;
  1: sqrt(7/10)*I + i*sqrt(3/10)*Z;
}
```

### Communication

```
do
  [] send: not d; c!m -> d := true;
  [] receive: p=0; c?r -> p := 1;
od
```

Each branch has an optional label, a classical guard, a send `c!e` or receive `c?x`, and a body.
A send and a receive on the same channel in different processes execute together.
Communication is synchronous.

## Writing a specification

```python
verify(precondition, program, postcondition, invariant=..., decreases=...)
```

Assertions are written `"{ classical ; quantum }"`.
`assertion(classical, quantum)` builds the same pair from two strings.

**Classical part.** `and`, `or`, `not`, `=>`, `<=>`, `=` and integer arithmetic.
`[c]` is the 0/1 indicator of condition `c`.
Phase specifications may also carry the paper's read-only domain `0 <= alpha and alpha < 2*pi`.
Other angle-dependent restrictions are not supported.

**Quantum part.**

| Predicate | Meaning |
|---|---|
| `I` | identity |
| `Bell[a,b]` | projector onto `(\|00⟩+\|11⟩)/√2` |
| `Zero[q]` | projector onto `\|0⟩` |
| `Plus[q]` | projector onto `\|+⟩` |
| `rho(psi)[q]` | projector `\|psi⟩⟨psi\|` for a declared state parameter |
| `rho(psi)[c,t]` | joint projector for a declared two-qubit state, in register order `c,t` |
| `Equator(alpha)[q]` | projector onto `(\|0⟩+exp(i*alpha)\|1⟩)/√2` |
| `P * Q` | tensor product of predicates on disjoint qubits |
| `U[q] * P` | `U P U†` |
| `U[q]^(e)` | `U` raised to an integer expression `e`, e.g. `Z[B]^((1-p)*m)` |

`state psi;` corresponds to a Rocq parameter `psi : Vector 2` with hypotheses `WF_Matrix psi` and `psi† * psi = I 1`.
It does not allocate an extra qubit or choose a particular input state.
Teleportation uses `rho(psi)[A1] * Bell[A2,B]` as its precondition and `rho(psi)[B]` as its postcondition, matching the three-qubit specification in [Teleportation.v](../../CaseStudies/Teleportation.v).
The check is symbolic for every normalized `psi`, including the computational-basis states and complex relative phases.
Non-local CNOT declares `state psi[2];` and uses the paper's four-qubit specification `Bell[A,B] * rho(psi)[C,T]` to `CNOT[C,T] * rho(psi)[C,T]`.
Its joint input may be entangled, and neither example introduces reference qubits.

**Invariant.** Required for protocols with a `do ... od` loop.
It must hold after initialization and be preserved by every matching send/receive pair.

**Ranking function.** `decreases` is an integer expression over classical variables.
With it, VeriLocQ checks total correctness (`Distributed-tot`).
It also checks that the ranking is nonnegative, decreases at every communication, and that no deadlock occurs.
Without it, VeriLocQ checks partial correctness (`Distributed`).

## Reading the result

| Status | Meaning |
|---|---|
| `VERIFIED` | every obligation passed |
| `NOT_VERIFIED` | at least one obligation failed or could not be decided |
| `PASSED` | the obligation holds |
| `FAILED` | the obligation has a counterexample |
| `INCOMPLETE` | a budget was exceeded or no exact decision was possible. This never counts as success. |

A `FAILED` obligation can come from an unsuitable invariant.
It does not by itself show that the final specification is false.
Malformed or unsupported input raises `SourceError` or `Unsupported`.

For more detail on a result

- `result.details()` lists each obligation with its checked case count and the method that decided it.
- `result.explain()` expands the backward predicate calculations, intermediate W predicates, measurement-outcome sums and solver conditions.
- `result.explain(matrices=True)` also shows the recorded precondition, WP and residual matrices.
  The displayed valuation illustrates one case of the exhaustive check.

### A failing example

Deleting Bob's Z correction from RSP

```python
broken = program(rsp.source.replace("if r=1 then Z[B]; fi;", ""))
print(verify("{ 0 <= alpha and alpha < 2*pi ; Bell[A,B] }", broken, "{ 0 <= alpha and alpha < 2*pi ; Equator(alpha)[B] }",
             invariant="{ 0 <= alpha and alpha < 2*pi and (d <=> p=1) ; Z[B]^((1-p)*m) * Equator(alpha)[B] }",
             decreases="1-[d]"))
```

gives

```
NOT_VERIFIED (total correctness)
FAILED: Invariant preserved: Alice.send ↔ Bob.receive
  The precondition does not guarantee this intermediate proof condition. The program or the supplied invariant may need to change.
  Example input: {'m': 1, 'd': False, 'r': 1, 'p': 0}
```

The example input names the classical values where the obligation fails.
Here Alice measured `m=1`, the outcome that needs the deleted correction.

## Command line

The bundled case studies run from the command line.

```sh
.venv/bin/python -m verilocq --case all
.venv/bin/python -m verilocq --case rsp
.venv/bin/python -m verilocq --case rsp --omit Z
.venv/bin/python -m verilocq --case teleportation --audit-orders
.venv/bin/python -m verilocq --case distillation --omit-bilateral-gate Alice
.venv/bin/python -m verilocq --case all --json
```

| Option | Meaning |
|---|---|
| `--case NAME` | `rsp`, `phase-choice`, `teleportation`, `swapping`, `remote-cnot`, `distillation` or `all` |
| `--omit X` or `--omit Z` | delete a correction gate from the finite examples |
| `--omit-bilateral-gate Alice` or `Bob` | delete a local CNOT from distillation |
| `--audit-orders` | also check both complete message orders in the finite examples |
| `--json` | print one JSON document |

The exit code is 0 when every selected case is verified and 1 otherwise.

Tests

```sh
.venv/bin/python -m unittest discover -s tests -v
```

## Notebook

[Quickstart.ipynb](Quickstart.ipynb) defines every case study in full, followed by its specification and `verify` call.
The order is RSP, a broken RSP, teleportation, entanglement swapping, non-local CNOT, distillation and PhaseChoice.
The Notebook is stored without outputs.
Run it in Jupyter, or execute and save it with

```sh
.venv/bin/python scripts/execute_notebook.py
```

Runtime files stay in `.runtime/`.
`scripts/build_notebook.py` regenerates the Notebook from its source.

## Case studies

| `--case` | Protocol | Verified property | Paper |
|---|---|---|---|
| `rsp` | Remote state preparation | Bob holds `Equator(alpha)` for every angle | App. C.2 |
| `phase-choice` | Scheduler-selected phase rotations | the output follows the recorded choice | App. C.3 |
| `teleportation` | Teleportation | identity channel on arbitrary inputs, both message orders | §6.1, App. B.1 |
| `swapping` | Entanglement swapping | remote Bell pair, both message orders | §6.2, App. B.2 |
| `remote-cnot` | Non-local CNOT | CNOT on an arbitrary normalized joint input, including entangled inputs | App. C.1 |
| `distillation` | BBPSSW distillation, unbounded retries | both first-acceptance specifications for every horizon `n` | §6.3, App. B.3 |

Distillation uses dedicated forms.
The preconditions are `E_pass(0,n)` and `E_good(0,n)`, and the invariants use `K_pass(...)` and `K_good(...)`.
The classical invariant includes `kA<n`, as in the paper.
The parameter `n` is a proof horizon, not an execution limit, and the triples concern first-acceptance mass rather than termination on every possible resource state.
These forms apply to the BBPSSW retry controller only.
After verification, `distill_good.bounds(fidelity="4/5", attempts=5)` returns the acceptance and Bell-overlap bounds for independent Werner pairs.
`trace_retry(distill, [(0,1),(1,1)])` follows the controller through given measurement outcomes.
The Notebook contains both verification calls and the probability and fidelity bounds.

## Scope

- At most six qubits in the finite-register engine.
- Finite classical domains (`bit`, `bool`, bounded `int`).
- Gates `H`, `X`, `Z`, `CNOT`, `R(alpha)` and exact one-qubit gate families.
- Unbounded arrays and counters only through the distillation controller.
- Invariants and ranking functions are supplied by the user.
- Results are checked by this Python implementation together with Z3 and SymPy.
  They are not checked by Rocq.

## TODO

- **Output goals.** Export the proof obligations of a triple as Rocq goals.
  Not implemented.

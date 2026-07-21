# LocQHL — Rocq mechanization

A Hoare-style program logic for **LOCC** (Local Operations and Classical
Communication) quantum protocols: the language, its operational semantics, the
assertion language, and the proof system, mechanized in Rocq.

## Build

```sh
make            # builds QuantumLib (vendored) then Core/
```

Requires the Rocq Prover (tested with 9.1). The vendored
`third_party/QuantumLib` is compiled as part of the project; nothing else is
needed.

## Layout (`Core/`, in dependency order)

| File | Contents |
| --- | --- |
| `Names.v` | finite name sets (footprint bookkeeping) |
| `Syntax.v` | expressions, local blocks, communication actions, `process`, `program`; program-variable footprints |
| `QuantumActions.v` | meaning of the quantum primitives (`U`, `q:=|0>`, measurement) over density matrices |
| `SemanticDomain.v` | classical stores, cq-states, cq-ensembles, mixed configurations, `terminal` / `collapse` / `norm` |
| `Semantics.v` | the fixed structure `Σ`, the local step `→ₗ`, the distributed step `⇝`, the mixed-configuration step, and the terminal semantics `Term` |
| `Assertions.v` | cq-assertions (deep embedding), satisfaction `degree`, entailment `⊨`, and validity `⊨ {{P}} · {{Q}}` |
| `WellFormed.v` | footprints of program phrases and the well-formedness conditions of a distributed program |
| `Rules.v` | the proof system: `local_derivable` (7 local rules) and `derivable` (Par-Disjoint-MP, Par-Comp-MP, Comm-Done, Comm-Select-MP, Branch-Accum, Conseq) |

## Status

- **Definitions:** language, operational semantics through `Term`, deep
  assertion language, validity, well-formedness, and all 12 proof rules are
  defined and the whole thing builds clean. Only axioms are the two Rocq real
  numbers carry (`sig_forall_dec`, `functional_extensionality_dep`).
- **Proofs:** soundness (`derivable → valid`) and the case studies are not yet
  done.

### Known gaps to close before soundness

- **`wf_interp`** — measurement completeness `Σ_m Mₘ† Mₘ = I` is not yet
  imposed on `interp`; Meas and Branch-Accum soundness depend on it.
- **`q_add` semantics** — the "undefined if a summand is" choice and the
  summability needed to keep a sum an effect must be checked against the paper.
- **`wf ⟹ DisjMP`** — the theorem that makes Par-Disjoint-MP premise-free.

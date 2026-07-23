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
| `Assertions.v` | cq-assertions (deep embedding), satisfaction `degree`, entailment `⊨[Σ]`, and validity `Σ ⊨ {{P}} · {{Q}}` over genuine quantum states |
| `TraceFacts.v` | the Löwner-order/trace bridge (trace nonnegativity of positive pairings via the spectral theorem, monotonicity of `degree` under entailment) and closure of state legitimacy under the quantum actions |
| `WellFormed.v` | footprints of program phrases and the well-formedness conditions of a distributed program |
| `Rules.v` | the proof system: `local_derivable` (`⊢ₗ`, 7 local rules) and `derivable` (`⊢ₚ`: Par-Disjoint-MP, Par-Comp-MP, Comm-Done, Comm-Select-MP, Branch-Accum, Conseq) |
| `Soundness.v` | soundness of the proof system: preservation of state legitimacy along execution (`term_preservation`), the per-rule validity obligations, and the assembly of the top-level soundness theorem |

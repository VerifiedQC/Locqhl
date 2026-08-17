# LocQHL — a Rocq mechanization of a Hoare-style logic for LOCC quantum protocols

[![CI](https://github.com/VerifiedQC/Locqhl/actions/workflows/ci.yml/badge.svg)](https://github.com/VerifiedQC/Locqhl/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![Rocq](https://img.shields.io/badge/Rocq-9.1-orange.svg)](https://rocq-prover.org/)
[![admits](https://img.shields.io/badge/admits-0-brightgreen.svg)](#status)
[![soundness](https://img.shields.io/badge/soundness-machine--checked-brightgreen.svg)](Core/Soundness.v)

A Hoare-style program logic for **LOCC** (Local Operations and Classical
Communication) quantum protocols — the language, its operational semantics, the
assertion language, and the proof system — fully mechanized in the
[Rocq Prover](https://rocq-prover.org/).

## Highlights

- **Machine-checked soundness.** The top-level soundness theorem
  (`Core/Soundness.v`) is proved end to end: state legitimacy is preserved
  along execution and every proof rule discharges its validity obligation.
- **No admits.** The `Core/` development and every `CaseStudies/` protocol
  contain zero `admit`/`Admitted` — the results hold under Rocq's standard
  axioms only.
- **Schedule independence as a theorem.** For well-formed distributed programs,
  confluence of the interleaving semantics is proved, not assumed.
- **Four worked protocols, mechanized end to end** under the logic
  (`CaseStudies/`): quantum teleportation, entanglement swapping, a non-local
  CNOT, and entanglement distillation — each with a completeness counterpart.

## Build

```sh
make            # builds QuantumLib (vendored) then Core/ and CaseStudies/
```

Requires the Rocq Prover (tested with **9.1**). The vendored
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
| `SoundnessFacts.v` | the supporting metatheory: trajectory commutation, schedule normalization, and the degree algebra |
| `Soundness.v` | soundness of the proof system: preservation of state legitimacy along execution (`term_preservation`), the per-rule validity obligations, and the assembly of the top-level soundness theorem |

### Case studies (`CaseStudies/`)

| Protocol | Correctness | Completeness |
| --- | --- | --- |
| Quantum teleportation | `Teleportation.v` | `BellComplete.v` |
| Entanglement swapping | `EntanglementSwapping.v` (`entanglement_swapping`) | `SwapComplete.v` |
| Non-local CNOT | `NonlocalCNOT.v` (`nonlocal_cnot`) | `NonlocalCNOTComplete.v` |
| Entanglement distillation | `Distillation.v` (`distillation_acc`) | `DistillationComplete.v` |

## Status

The proof development is complete with **no admits** and depends only on Rocq's
standard axioms. See `Core/Soundness.v` for the top-level soundness theorem and
`CaseStudies/` for the four mechanized protocols.
These claims can be regenerated at any time:

| Script | Purpose |
| --- | --- |
| `scripts/manifest.sh` | machine-generated proof manifest: every definition and lemma, with file, line, and proof status |
| `scripts/check-admits.sh` | the CI admit gate (rejects commits introducing admitted proofs) |
| `scripts/check-assumptions.sh` | `Print Assumptions` on the main theorems: prints the exact axiom closure |

## License

Licensed under the [Apache License, Version 2.0](LICENSE).
The vendored [QuantumLib](https://github.com/inQWIRE/QuantumLib) under
`third_party/` retains its own license.

## Citation

If you use LocQHL in your research, please cite it. A machine-readable
[`CITATION.cff`](CITATION.cff) is provided; a BibTeX entry:

```bibtex
@software{locqhl,
  title  = {{LocQHL}: A Rocq Mechanization of a Hoare-Style Program Logic for
            {LOCC} Quantum Protocols},
  author = {Chang, Le and Tao, Runzhou},
  year   = {2026},
  url    = {https://github.com/VerifiedQC/Locqhl},
  note   = {Apache-2.0}
}
```

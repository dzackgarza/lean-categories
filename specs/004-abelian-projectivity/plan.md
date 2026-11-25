# Implementation Plan: Abelian projectivity for polarized complex tori

**Branch**: `004-abelian-projectivity` (work lands on `main`) | **Date**: 2026-11-25 | **Spec**: [spec.md](spec.md)
**Input**: Feature specification from `specs/004-abelian-projectivity/spec.md`

Revision of record: `533e9259`. Decisions D1–D6 are in [research.md](research.md); the validation
runs in [quickstart.md](quickstart.md).

## Summary

From the existing complex tori with Riemann forms and the existing projective-variety predicate, the
feature builds holomorphic line bundles and Picard data, proves Appell–Humbert, constructs theta
sections, proves the Lefschetz very-ampleness theorem and the closed embedding into projective
space, and concludes with Chow's theorem and the comparison of the torus with the complex points of
a projective variety.

## Technical Context

**Language/Version**: Lean 4, toolchain of `lean-toolchain`
**Primary Dependencies**: Mathlib (complex manifolds, vector bundles, analytic functions)
**Storage**: Lean source under `LeanCategories/` (`Lattices/Valued/ComplexTorus.lean`,
`Schemes/Varieties.lean`, new owners under `LeanCategories/Geometry/` by M4)
**Testing**: tier-1 elaboration of each changed module; `just test` at the milestone
**Target Platform**: Linux, research image `ghcr.io/dzackgarza/sage:develop`
**Project Type**: Lean library (formal mathematics)
**Performance Goals**: tier-1 loop of each change under 300 s
**Constraints**: one Lean process under `flock .tmp/lean.lock`; no `sorry`, no project axiom
**Scale/Scope**: 4 success criteria; 10 tasks

## Constitution Check

| Article | Check for this feature | Status |
| --- | --- | --- |
| M1, M2 | Each statement read from its source (D4); no easier statement replaces the theorem | Contract O of feature 003 |
| M3 | No `sorry`, no project axiom | milestone gate |
| M4 | Line bundles on complex manifolds at their owner; tori and projective space as instances | D5 |
| M5, M6 | Total constructions; the chosen polarization and semicharacter are data | FR-003 |
| M7 | No registry row is added by this feature | none |
| M8 | Search before authoring; Mathlib vector bundles first | D5 |
| M9 | No consumer request is waiting on this feature | none |
| M10 | Content changes to FOUNDATIONS go to the mathematician | none planned |
| M11 | Executed as 002 T111 | D2 |
| M12, M13 | Records under LC-05, LC-11, LC-12; independent review | Contract O |
| E1, E2, E4, E10 | Tier 1 per change; positive and separating examples; one Lean process | Contract O |
| E3 | No contribution policy changes in this feature | none |
| E5 | One platform: Linux and the research image | Technical Context |
| E6, E7 | Durable logs and timing records | feature 001 T002, T003 |
| E8 | No optimization without a triage table | none |
| E9 | Construction of a torus, a bundle or an embedding close to instant | Contract O |

Gate result: pass.

## Contract

Each task applies Contract O of [feature 003](../003-arithmetic-lattice-foundations/plan.md#unit-contract):
source statement read first, search, owner at its generating category, comparison theorems,
positive and separating examples, FOUNDATIONS status paragraphs, tier 1, independent review.

## Project Structure

```text
specs/004-abelian-projectivity/
├── spec.md
├── plan.md
├── research.md          # decisions D1–D6
├── quickstart.md
├── checklists/
│   └── requirements.md
└── tasks.md
```

**Structure Decision**: no new directory outside `LeanCategories/Geometry/` and the existing owners.

## Complexity Tracking

No constitution violation needs justification.

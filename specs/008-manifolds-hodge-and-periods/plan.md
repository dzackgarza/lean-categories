# Implementation Plan: Manifolds, Hodge theory and period constructions

**Branch**: `008-manifolds-hodge-and-periods` (work lands on `main`) | **Date**: 2026-11-25 | **Spec**: [spec.md](spec.md)
**Input**: Feature specification from `specs/008-manifolds-hodge-and-periods/spec.md`

Revision of record: `a3a66fba`. Decisions D1–D9 are in [research.md](research.md); the
validation runs in [quickstart.md](quickstart.md).

## Summary

In task order: the sources; $\Omega_T$ as a complex manifold with the action of $O^+(T)$; the
quotient stack and coarse quotient; Heegner divisors; local systems, monodromy and markings;
polarized variations of Hodge structure; period maps; the Coble target; the Baily–Borel
compactification; toroidal data; semitoroidal compactifications; Kulikov degenerations; their
integral-affine dual complexes; the lattices of a surface; Mordell–Weil lattices; registry rows;
the milestone.

## Technical Context

**Language/Version**: Lean 4, toolchain of `lean-toolchain`
**Primary Dependencies**: Mathlib (`Geometry/Manifold`, `Analysis/Complex`, `QuadraticForm/Signature`, `Topology/Covering`)
**Storage**: Lean source under `LeanCategories/Geometry/`, `LeanCategories/Analytic/` and `LeanCategories/Lattices/Valued/`
**Testing**: tier-1 elaboration of each changed module and its test module; `just test` at the milestone
**Target Platform**: Linux, research image `ghcr.io/dzackgarza/sage:develop`
**Project Type**: Lean library (formal mathematics)
**Performance Goals**: tier-1 loop of each change under 300 s
**Constraints**: one Lean process under `flock .tmp/lean.lock`; no `sorry`, no project axiom
**Scale/Scope**: 2 issues; 16 requirements; 17 tasks

## Constitution Check

| Article | Check for this feature | Status |
| --- | --- | --- |
| M1, M2 | Each statement read from its source (D4–D9) | Contract O of feature 003 |
| M3 | No `sorry`, no axiom; no deep theorem stands as an axiom | D1; T017 |
| M4 | Period domains on the lattice owner; analytic objects on the analytic owner | Files per task |
| M5, M6 | Chosen components, markings and cone decompositions are data | FR-001, FR-006, FR-009 |
| M7 | Registry rows of the new categories | T016 |
| M8 | Search before authoring | Contract O |
| M9 | Consumer intake, at once | D1 |
| M10–M13 | Independent review; records under LC-05, LC-11, LC-12 | Contract O |
| E1–E10 | Tier 1 per change; logs and timing of feature 001 T001–T003 | Checks |

Gate result: pass.

## Current source state

Observed at `a3a66fba` by name search; each task starts from the source at its own revision.

| Item | In the source | Missing |
| --- | --- | --- |
| Type-IV domains | `Lattices/Valued/{PeriodDomainData,K3PeriodDomainData}.lean` (003 T037 owns the set level) | complex-manifold structure; group action; quotient stack |
| Baily–Borel | name hits in 10 modules | the boundary poset and the Proj construction at one owner |
| local systems, VHS | none found by name | all of FR-004, FR-005 |
| Kulikov | none found by name | all of FR-011, FR-012 |
| Néron–Severi | name hits (`Picard`) in 15 modules | the lattice extraction of FR-013 |
| Mordell–Weil | none found by name | all of FR-014 |

## Contract

Each task applies Contract O of [feature 003](../003-arithmetic-lattice-foundations/plan.md#unit-contract).

## Project Structure

```text
specs/008-manifolds-hodge-and-periods/
├── spec.md
├── plan.md
├── research.md
├── quickstart.md
├── checklists/requirements.md
└── tasks.md
```

**Structure Decision**: period domains and lattice extraction at the lattice owners; local
systems, variations, period maps, compactifications and degenerations under `Geometry/` and
`Analytic/` (M4).

## Complexity Tracking

No constitution violation needs justification.

# Implementation Plan: Scheme and stack geometry

**Branch**: `007-scheme-and-stack-geometry` (work lands on `main`) | **Date**: 2026-11-25 | **Spec**: [spec.md](spec.md)
**Input**: Feature specification from `specs/007-scheme-and-stack-geometry/spec.md`

Revision of record: `a3a66fba`. Decisions D1–D10 are in [research.md](research.md); the
validation runs in [quickstart.md](quickstart.md).

## Summary

In task order: the sources; schemes over a base and morphism properties; varieties and their
dimension family; coherent and reflexive sheaves, divisors and dualizing data; blowups, cyclic
covers, quotients and resolutions; fibred categories and stacks; algebraic spaces and stacks;
actions, torsors and quotient stacks; moduli problems; deformation theory; log pairs and
singularity classes; stable pairs and families; the KSBA moduli stack and its Coble instance;
stable graphs and $\overline{\mathcal M}_{g,n}$; registry rows; the milestone.

## Technical Context

**Language/Version**: Lean 4, toolchain of `lean-toolchain`
**Primary Dependencies**: Mathlib (`AlgebraicGeometry.Scheme`, `Morphisms/*`, `Sites/*`, `IsStack`, `Functor.IsFibered`, `Extension.cotangentComplex`)
**Storage**: Lean source under `LeanCategories/AlgebraicGeometry/` and `LeanCategories/Schemes/`
**Testing**: tier-1 elaboration of each changed module and its test module; `just test` at the milestone
**Target Platform**: Linux, research image `ghcr.io/dzackgarza/sage:develop`
**Project Type**: Lean library (formal mathematics)
**Performance Goals**: tier-1 loop of each change under 300 s
**Constraints**: one Lean process under `flock .tmp/lean.lock`; no `sorry`, no project axiom
**Scale/Scope**: 3 issues; 16 requirements; 20 tasks

## Constitution Check

| Article | Check for this feature | Status |
| --- | --- | --- |
| M1, M2 | Each definition read from its source (D3, D4, D7, D8) | Contract O of feature 003 |
| M3 | No `sorry`, no axiom; no deep theorem stands as an axiom | D2; T020 |
| M4 | Properties on morphisms; curves and surfaces as values of one family | FR-001, FR-002 |
| M5, M6 | Total constructions; chosen data (roots of covers, atlases) are data | FR-004, FR-006 |
| M7 | Registry rows of the new categories; no duplicate of 001's rows | T019 |
| M8 | Search before authoring; Mathlib first | Contract O |
| M9 | Consumer intake, at once | D1 |
| M10–M13 | Independent review; records under LC-05, LC-11, LC-12 | Contract O |
| E1–E10 | Tier 1 per change; logs and timing of feature 001 T001–T003 | Checks |

Gate result: pass.

## Current source state

Observed at `a3a66fba` by module listing and name search; each task starts from the source at its
own revision.

| Item | In the source | Missing |
| --- | --- | --- |
| relative Spec and Proj | `AlgebraicGeometry/RelativeSpec/`, `AlgebraicGeometry/RelativeProj/` (#22) | none for this feature |
| varieties | `Schemes/Varieties.lean`, `AlgebraicGeometry/ClassicalVariety.lean` | comparison with D3; the dimension family |
| divisors | `Schemes/Divisors.lean` and data modules (corpus units pending in 002 T029, T030) | reflexive powers; $\mathbb Q$-divisors; demi-normal data |
| blowups | name hits in 7 modules | the universal property at its owner |
| stacks | `IsStack` uses in 25 modules | algebraic spaces and stacks, quotient stacks, moduli problems |
| pairs and KSBA | none found by name | all of FR-010–FR-013 |
| stable graphs | none found by name | all of FR-014 |

## Contract

Each task applies Contract O of [feature 003](../003-arithmetic-lattice-foundations/plan.md#unit-contract).

## Project Structure

```text
specs/007-scheme-and-stack-geometry/
├── spec.md
├── plan.md
├── research.md
├── quickstart.md
├── checklists/requirements.md
└── tasks.md
```

**Structure Decision**: schemes and sheaves under `AlgebraicGeometry/` and `Schemes/`; stacks,
moduli and pairs under a new `AlgebraicGeometry/Stacks/` and `AlgebraicGeometry/Pairs/` (M4).

## Complexity Tracking

No constitution violation needs justification.

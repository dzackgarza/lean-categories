# Implementation Plan: The algebraic categories of the catalogue

**Branch**: `009-algebraic-category-catalogue` (work lands on `main`) | **Date**: 2026-11-25 | **Spec**: [spec.md](spec.md)
**Input**: Feature specification from `specs/009-algebraic-category-catalogue/spec.md`

Revision of record: `a3a66fba`. Decisions D1–D8 are in [research.md](research.md); the validation
runs in [quickstart.md](quickstart.md). Paths are relative to `LeanCategories/`. `Sem/` is
`Catalogue/Semantics/`.

## Summary

In task order: the divisibility tower; certified free-plus-torsion modules and their operation
table; quotients, ideals and fractional ideals; localization, completion and the regular module;
groups, actions and presentations; finite abelian decompositions; $G$-modules; finitely generated
groups; chain complexes and cohomology; graded and differential graded algebras; registry rows;
the milestone.

## Technical Context

**Language/Version**: Lean 4, toolchain of `lean-toolchain`
**Primary Dependencies**: Mathlib (`RingTheory`, `Algebra/Category`, `GroupTheory/PresentedGroup`, `RepresentationTheory/Rep`, `Algebra/Homology`, `LinearAlgebra/CliffordAlgebra`)
**Storage**: Lean source under `LeanCategories/Algebra/`, `RingTheory/`, `Modules/`, `Homological/` and `Catalogue/Semantics/`
**Testing**: tier-1 elaboration of each changed module and its test module; `just test` at the milestone
**Target Platform**: Linux, research image `ghcr.io/dzackgarza/sage:develop`
**Project Type**: Lean library (formal mathematics and its registry)
**Performance Goals**: tier-1 loop of each change under 300 s
**Constraints**: one Lean process under `flock .tmp/lean.lock`; no `sorry`, no project axiom
**Scale/Scope**: 8 issues; 11 requirements; 14 tasks

## Constitution Check

| Article | Check for this feature | Status |
| --- | --- | --- |
| M1, M2 | Every category is mathematics of this repository, read from its source | Contract F of feature 005 |
| M3 | No `sorry`, no project axiom | T014 |
| M4 | Each category at its generating level; inheritance by structural functors | FR-001, FR-010 |
| M5, M6 | Total operations; chosen normalizations, Euclidean structures and splittings are data | D2, D3 |
| M7 | One registry row per category; corpus owners reused | FR-008, FR-010 |
| M8 | Search before authoring, recorded in the issue | Contract F |
| M9 | Feature 001 T068 takes T001 at once | D1 |
| M10–M13 | Independent review; records | Contract F |
| E1–E10 | Tier 1 per change; logs and timing of feature 001 T001–T003 | Checks |

Gate result: pass.

## Current source state

Observed at `a3a66fba` by listing the category IDs of the registry and module names.

| Item | In the source | Missing |
| --- | --- | --- |
| divisibility tower | `cat.commutative_rings`, `cat.fields`, `cat.division_rings`; `Algebra/Euclidean.lean` | `cat.integral_domains`, UFDs with normalization, PIDs, Euclidean domains |
| ideals and fractions | `cat.ideals_r`; `Algebra/{Ideals,FractionalIdeals}.lean` | quotient constructor with its universal property; localization and completion rows |
| groups | `cat.groups`, `cat.subobjects_groups`, `cat.arrows_groups`, `cat.core_groups`; `Algebra/{GroupKernel,GroupProduct,GroupPullback}.lean` | $G$-sets, presentations, invariant factors |
| modules | `cat.modules_r`, `cat.torsion_free_modules`, `cat.freemodules`, `cat.finitelygeneratedmodules` | certified splittings; $G$-modules |
| complexes | `Homological/`, `Modules/ChainComplexModel.lean` | registry rows of the complex category and homology functors |
| algebras | `cat.algebras`; `Algebra/{GradedAntiderivation,FreeAlgebras}.lean` | graded, dg, Clifford and exterior rows |

## Project Structure

```text
specs/009-algebraic-category-catalogue/
├── spec.md
├── plan.md
├── research.md
├── quickstart.md
├── checklists/requirements.md
└── tasks.md
```

**Structure Decision**: the existing owners; rows in `Catalogue/Semantics/Algebra/` and
`Catalogue/Semantics/Modules/`.

## Complexity Tracking

No constitution violation needs justification.

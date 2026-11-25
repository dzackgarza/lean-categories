# Implementation Plan: Reflection, fan and toric geometry

**Branch**: `006-reflection-and-toric-geometry` (work lands on `main`) | **Date**: 2026-11-25 | **Spec**: [spec.md](spec.md)
**Input**: Feature specification from `specs/006-reflection-and-toric-geometry/spec.md`

Revision of record: `a3a66fba`. Decisions D1–D8 are in [research.md](research.md); the
validation runs in [quickstart.md](quickstart.md).

## Summary

From the chambers, cones and fans on `main`, the feature folds Lorentzian chambers, adds the
bounded Vinberg computation, coarsens Coxeter fans by the Wythoff construction, realizes fans as
toric schemes by a covariant functor, and defines the charge of Looijenga pairs.

## Technical Context

**Language/Version**: Lean 4, toolchain of `lean-toolchain`
**Primary Dependencies**: Mathlib (`PointedCone`, `CoxeterSystem`, `AlgebraicGeometry.Scheme`, `MonoidAlgebra`)
**Storage**: Lean source under `LeanCategories/Lattices/Valued/` (folding, Vinberg, Wythoff) and `LeanCategories/AlgebraicGeometry/Toric/`
**Testing**: tier-1 elaboration of each changed module and its test module; `just test` at the milestone
**Target Platform**: Linux, research image `ghcr.io/dzackgarza/sage:develop`
**Project Type**: Lean library (formal mathematics)
**Performance Goals**: tier-1 loop of each change under 300 s
**Constraints**: one Lean process under `flock .tmp/lean.lock`; no `sorry`, no project axiom
**Scale/Scope**: 3 issues; 10 requirements; 14 tasks

## Constitution Check

| Article | Check for this feature | Status |
| --- | --- | --- |
| M1, M2 | Each statement read from its source (D1, D3, D6) | Contract O of feature 003 |
| M3 | No `sorry`, no project axiom; Vinberg claims no termination | D2; T014 |
| M4 | Folding on the lattice owner; toric schemes on schemes | Files per task |
| M5, M6 | Total computations; chosen chambers and bounds are data | D2 |
| M7 | Registry rows of the new categories | T012 |
| M8 | Search before authoring | Contract O |
| M9 | Consumer intake of the research programme, at once | D7 |
| M10–M13 | Independent review; records under LC-05, LC-11, LC-12 | Contract O |
| E1–E10 | Tier 1 per change; logs and timing of feature 001 T001–T003 | Checks |

Gate result: pass.

## Current source state

Observed at `a3a66fba` by module listing and name search; each task starts from the source at its
own revision.

| Item | In the source | Missing |
| --- | --- | --- |
| folding | `Lattices/Valued/{FoldingWitness,FoldingChamberImage,FoldingRootTransferEquivalence,FoldingInvariantChamberOfAmbientSigns,FoldingE10Rigidity}.lean` and tests | the general statement for signature $(1, n)$; the published worked example; build membership (002 T130) |
| Vinberg | `Lattices/Valued/{VinbergE10Roots,VinbergE10Chamber}.lean` | the bounded algorithm on a general datum |
| Wythoff | `Lattices/Valued/{WythoffSemifan,WythoffCoarsenedFamily,FanCoarsening}.lean`, `ForMathlib/RootSystem/WythoffAscent.lean` | the functor and its laws (after 002 T121) |
| toric | `AlgebraicGeometry/Toric/AffineToric.lean` (`coneDual`, `affineToricScheme`, `affineToricRingMap`) | the open immersion of a face; the colimit; the functor |
| Looijenga pairs | none found by name | the pair, charge and blowup theorems |

## Contract

Each task applies Contract O of [feature 003](../003-arithmetic-lattice-foundations/plan.md#unit-contract).

## Project Structure

```text
specs/006-reflection-and-toric-geometry/
├── spec.md
├── plan.md
├── research.md
├── quickstart.md
├── checklists/requirements.md
└── tasks.md
```

**Structure Decision**: no new directory outside `AlgebraicGeometry/Toric/` and the existing
lattice owners.

## Complexity Tracking

No constitution violation needs justification.

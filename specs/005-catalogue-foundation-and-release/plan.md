# Implementation Plan: Classifier foundation, proof-carrying registry and catalogue release

**Branch**: `005-catalogue-foundation-and-release` (work lands on `main`) | **Date**: 2026-11-25 | **Spec**: [spec.md](spec.md)
**Input**: Feature specification from `specs/005-catalogue-foundation-and-release/spec.md`

Revision of record: `a3a66fba`. Decisions D1–D17 are in [research.md](research.md); the schema
additions in [data-model.md](data-model.md); the validation runs in [quickstart.md](quickstart.md).
Paths are relative to `LeanCategories/`. `Reg/` is `Catalogue/Registry/`. `Sem/` is
`Catalogue/Semantics/`.

## Summary

The feature makes the registry's foundation mathematical and releases it. In task order: the
classifier, its reindexing universal property and the algebraic testbed; proof-carrying rows and
generic evaluation; typed constructors and families; operations and methods as checked functors;
the standard categorical vocabulary; the vertical slices; the export and the Foundation 0.1
release; the Lattice arithmetic 0.2 release; the certification of the complete catalogue; the
publication to Prove2Me.

## Technical Context

**Language/Version**: Lean 4, toolchain of `lean-toolchain`
**Primary Dependencies**: Mathlib (`rev = "master"`, locked in `lake-manifest.json`)
**Storage**: Lean source; registry rows through `normalized_registry`; release JSON and DOT
generated from `RegistrySnapshot`
**Testing**: Lean test modules (`Reg/*Tests.lean`, `Sem/*Tests.lean`, `CategoryTheory/OneCat/*Tests.lean`) with `example`, `#guard_msgs` and theorems; `just test` at the milestone
**Target Platform**: Linux, research image `ghcr.io/dzackgarza/sage:develop` (constitution E5)
**Project Type**: Lean library (formal mathematics and its registry)
**Performance Goals**: tier-1 loop of each task under 300 s (constitution E1, E4)
**Constraints**: one Lean process under `flock .tmp/lean.lock` (E10); no `sorry`, no project axiom (M3)
**Scale/Scope**: 10 issues; 24 requirements; 26 tasks

## Constitution Check

| Article | Check for this feature | Status |
| --- | --- | --- |
| M1 | Every classifier, row, constructor, family, operation and method is mathematics of this repository | pass |
| M2 | Each statement is read from FOUNDATIONS or its cited source | Contract F |
| M3 | No `sorry`, no axiom; `just test` at the milestone | Contract F; T026 |
| M4 | Operations at their generating category; inheritance by structural functors | FR-014, FR-015 |
| M5 | Total operations; numerals as universal images | FR-014 |
| M6 | Comparison cells are data; chosen structure never from existence | FR-003, FR-008, FR-015 |
| M7 | One field per meaning; the export comes from the registry | data-model.md; FR-010, FR-019 |
| M8 | Search before authoring, recorded in the issue | Contract F, step 2 |
| M9 | Consumer requests of the kernel go to feature 001; none waits here | Assumptions |
| M10 | Independent review of each change | Contract F, step 7 |
| M11 | This task list in document order | Execution order |
| M12, M13 | Records under LC-05, LC-11, LC-12; no artifact certifies itself | Contract F |
| E1–E10 | Tier-1 loop, logs and timing of feature 001 T001–T003; one Lean process | Checks |

Gate result: pass. No violation is justified in Complexity Tracking.

## Checks of this repository

The tiers, commands and preconditions are those of feature 001
([plan.md](../001-catalogue-inputs-for-the-cas/plan.md#checks-of-this-repository)): tier 1 is
`just loop <modules>` after 001 T001, otherwise `flock .tmp/lean.lock lake env lean <module>`;
the full gate is `just test`.

## Current source state

Observed at `a3a66fba` by module listing and name search. Each task starts from the source at
its own revision (Contract F, step 3).

| Item | In the source | Missing |
| --- | --- | --- |
| classifier | `CategoryTheory/OneCat/Classifier.lean` (`Classifier` over `ObjCat`, `PropertyClassifier` with `full`, `faithful`) | ambient interface; repleteness; abbreviation form |
| reindexing | `CategoryTheory/OneCat/{Reindex,CategoricalPullback}.lean` (`reindex`, `ReindexIdIso`, `ReindexCompIso` as structures) | universal property, identity, composition and pasting as theorems; actual 2-cells |
| operation and extension classifiers | none found by name | `Op_n`, diagram-extension classifiers, matching hook |
| algebraic testbed | `Algebra/Concrete/Magmas.lean` (`UnitalMagmaWithInv`) | $E_1$ grounding; role equivalences; inverse classifier on monoids |
| registry rows | `Catalogue/{Syntax,Interpretation,Realization}.lean`, `Reg/{Entry,Semantic,Snapshot}.lean` | denotation witness per row; generic evaluator; `canonicalize`; total and leg in `ClassifierEntry` |
| constructors | `Catalogue/Constructors.lean`, `Sem/ConstructorRegistration.lean` | typed signatures with morphism actions and evaluators |
| families | `CategoryFamilyEntry`; `cat.modules_r`, `cat.modules_total`, `cat.modules_over_rings_ext` | left, right, bi-, graded modules, vector spaces, algebra and ring ideals |
| cardinality | `fun.sets.cardinality`, `meth.cardinality` | the core functor form and its restriction; index; transporters |
| vocabulary | `AdjunctionEntry` (`left`, `right`, `declaration`); `CategoryTheory/Adjunction/Mates.lean` | unit, counit, triangles in the row; localizations; free-algebra rows; monoid-algebra recognition |
| slices | `obj.bil_wform.root_lattice_a_discriminant`, `mor.sets.matrix_det`, `op.enumerated_sets.ranked.nth` | the slice test modules |
| export and release | `Integration/RegistryConsumer/`; `Reg/Snapshot.lean` | JSON and DOT generation; release tags |
| publication | `scripts/publish_prove2me.py`, `scripts/extract_cards.py`, `Tools/ReferenceGraph.lean` | the cards beyond the emitted ones; the published run |

## Unit contract

**Contract F (foundation task).** For each requirement of the task:

1. Read the FOUNDATIONS anchor that the requirement cites and the Mathlib owner that the issue's
   reuse comment names, at the task revision.
2. Run the search of constitution M8 (Mathlib, the formalization corpus, the broader ecosystem)
   and record it in the owning issue.
3. Record which parts are present at the task revision (by declaration) and which are not.
4. Write each missing part at its generating owner (M4), with actual data for every comparison
   (M6) and no new field for a meaning that a field holds (M7).
5. Add the test module that the task names, with a positive example and a separating example
   drawn from the issue or the source.
6. Check: tier 1 on the changed modules and the test module; new modules in
   `LeanCategories/All.lean`; when a declaration realizes a corpus unit, its mapping row with
   `[realized]` and the regenerated definition index and frontier in the same commit
   (constitution M11).
7. Review: an author who did not write the change compares it with the source (M10).

## Phases and order

| Phase of tasks.md | Content | Requirements | Gate to leave |
| --- | --- | --- | --- |
| 1 | classifiers | FR-001–FR-006 | test modules green |
| 2 | proof-carrying registry | FR-007–FR-010 | every snapshot row evaluates with its witness |
| 3 | constructors and families | FR-011–FR-013 | test module green |
| 4 | operations and methods | FR-014, FR-015 | test module green |
| 5 | standard vocabulary | FR-016, FR-017 | test module green |
| 6 | vertical slices | FR-018 | slice module green |
| 7 | export and releases | FR-019–FR-021 | release tags reproduce |
| 8 | certification, publication, milestone | FR-022, FR-023 | coverage report complete; publication run |

The feature runs in its own document order beside feature 001 (constitution M11). Its tasks
name the 001 tasks whose rows they extend as inputs.

## Project Structure

### Documentation (this feature)

```text
specs/005-catalogue-foundation-and-release/
├── spec.md
├── plan.md
├── research.md
├── data-model.md
├── quickstart.md
├── checklists/requirements.md
└── tasks.md
```

### Source Code (repository root)

```text
LeanCategories/
├── CategoryTheory/OneCat/   # classifier, reindexing, pullback, ambient interface
├── Catalogue/               # syntax, interpretation, registry, semantics
├── Algebra/Concrete/        # algebraic testbed
├── Tools/                   # export, reference graph
└── All.lean
Integration/RegistryConsumer/
scripts/                     # publish_prove2me.py, extract_cards.py, export
```

**Structure Decision**: the existing layout. The classifier interfaces stay in
`CategoryTheory/OneCat/`; registry schema in `Catalogue/Registry/`.

## Complexity Tracking

No constitution violation needs justification.

# Tasks: Reflection, fan and toric geometry

**Input**: [spec.md](spec.md), [plan.md](plan.md), [research.md](research.md),
[quickstart.md](quickstart.md)

**Tests**: each task's check is the tier-1 elaboration of its modules and the theorems it names;
the milestone runs `just test`. Each task applies Contract O of feature 003.

Paths are relative to `LeanCategories/`.

## Format: `[ID] [P?] [Story] Description`

`[P]` marks a task whose drafting can run beside its neighbours; Lean checks run one at a time
(constitution E10). Inputs from other features are cited as "002 Tnnn".

## Execution order

Select issues in definition-first native tree order (constitution M11); within the selected
issue, execute tasks in prerequisite order (research D7).
Inside a phase, a task follows the tasks whose results it uses; the workstream does each input task first, in the feature or repository that owns it, and then returns (constitution M11).

## Phase 1: Folding (US1, #116)

- [ ] T001 [US1] #116: run the search of constitution M8 and record it in the issue; read through
  the live library the folding statement of arXiv:2312.03638 and of the source that it cites for
  folding, and record each item key and locator in the issue. Decision: D1.
- [ ] T002 [US1] #116 FR-001: the fixed sublattice $M^\sigma$ of an involution preserving a
  chamber of an even lattice of signature $(1, n)$, the folded root set, its Coxeter diagram and
  the chamber theorem, generalizing the folding modules on `main`. Files:
  `Lattices/Valued/{FoldingWitness,FoldingChamberImage,FoldingRootTransferEquivalence}.lean`.
  Inputs: T001. Decision: D1. Check: tier 1; a new `Lattices/Valued/FoldingTheoremTests.lean`
  with one positive and one separating example (an involution that preserves no chamber).
- [ ] T003 [US1] #116 FR-002: the worked declaration of one published folded diagram of
  arXiv:2312.03638, with its folded roots and diagram. Files: a new
  `Lattices/Valued/FoldingAEGSExample.lean`. Inputs: T002. Check: tier 1; the module is imported
  by `LeanCategories/All.lean`.

## Phase 2: Vinberg's algorithm and chamber faces (US2, #8)

- [ ] T004 [US2] #8 FR-003: Vinberg's algorithm as a total function of a Lorentzian reflection
  datum and a bound into `Option` of a walled fundamental chamber with its proof. Files: a new
  `Lattices/Valued/VinbergAlgorithm.lean`, `Lattices/Valued/VinbergE10Chamber.lean`. Decision: D2.
  Check: a new `Lattices/Valued/VinbergAlgorithmTests.lean`: the $E_{10}$ chamber is returned; a
  small bound returns `none`.
- [ ] T005 [US2] #8 FR-004: the correspondence of elliptic subdiagrams with faces and of
  parabolic subdiagrams with ideal vertices for the chambers of #23; the corrected
  $(2, 3, \infty)$ example (spec, Edge Cases) as a test. Files: `Lattices/Valued/WeylChambers.lean`
  and the chamber modules of #23. Check: tier 1 with the example's determinant $2$ and signature
  $(1, 2)$.

## Phase 3: The Wythoff coarsening (US3, #24)

- [ ] T006 [US3] #24 FR-005: the Wythoff coarsening as a functor from folded chamber data to fans,
  with group invariance and local finiteness. Files:
  `Lattices/Valued/{WythoffCoarsenedFamily,FanCoarsening}.lean`. Inputs: T002, 002 T121.
  Decision: D3. Check: a new `Lattices/Valued/WythoffFunctorTests.lean`.
- [ ] T007 [US3] #24: the comparison of the functor of T006 with the coarsened family of 002 T121
  at the AET examples; one owner remains. Inputs: T006. Check: tier 1.

## Phase 4: Toric schemes (US4, #24, #8)

- [ ] T008 [P] [US4] #24 FR-006: the open immersion $U_\tau \hookrightarrow U_\sigma$ of a face
  inclusion, from `affineToricRingMap` and Mathlib `IsOpenImmersion`. Files:
  `AlgebraicGeometry/Toric/AffineToric.lean`. Decision: D4. Check: a new
  `AlgebraicGeometry/Toric/AffineToricTests.lean`.
- [ ] T009 [US4] #24 FR-007: $X_\Sigma$ as the colimit over the face diagram of a fan
  (Mathlib `AlgebraicGeometry.Scheme.GlueData` or colimits of open immersions). Files: a new
  `AlgebraicGeometry/Toric/ToricScheme.lean`. Inputs: T008. Check: the fan of $\mathbb P^2$ gives
  $\mathbb P^2_k$ (feature 002 FC06 owner of projective space).
- [ ] T010 [US4] #24 FR-007: the covariant toric functor from fans to schemes over $k$ with its
  identity and composition laws. Files: `AlgebraicGeometry/Toric/ToricScheme.lean`. Inputs: T009.
  Decision: D4. Check: tier 1.
- [ ] T011 [P] [US4] #8 FR-008: Looijenga pairs, their charge and the blowup theorems, read from
  the source of D6. Files: a new `AlgebraicGeometry/Toric/LooijengaPair.lean`. Decision: D6.
  Check: the toric pair $(\mathbb P^2, \text{triangle})$ has charge $0$.

## Phase 5: Registry, status, milestone

- [ ] T012 FR-009: registry rows for folded chamber data, fans, toric schemes and Looijenga
  pairs with their structural functors. Files: `Catalogue/Semantics/Lattices/`,
  `Catalogue/Semantics/Algebra/Schemes.lean`. Inputs: T002, T010, T011. Check:
  `Catalogue/Registry/SnapshotTests.lean` lists the rows.
- [ ] T013 Update the "Lean realization status" paragraphs of `FOUNDATIONS.md` §§58–60 that this
  feature changes (feature 003 research D6). Inputs: T001–T012.
- [ ] T014 Milestone: every requirement of the spec holds, the success-criteria table is measured
  at the milestone revision, and `just test` passes. Performs no other work.

## Dependencies & Execution Order

- T001 before T002; T002 before T003, T006; T006 needs 002 T121; T008 before T009 before T010.
- T012 after T002, T010, T011; T014 last.

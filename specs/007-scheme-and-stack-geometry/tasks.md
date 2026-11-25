# Tasks: Scheme and stack geometry

**Input**: [spec.md](spec.md), [plan.md](plan.md), [research.md](research.md),
[quickstart.md](quickstart.md)

**Tests**: each task's check is the tier-1 elaboration of its modules and the theorems it names;
the milestone runs `just test`. Each task applies Contract O of feature 003.

Paths are relative to `LeanCategories/`.

## Format: `[ID] [P?] [Story] Description`

`[P]` marks a task whose drafting can run beside its neighbours; Lean checks run one at a time
(constitution E10). Inputs from other features are cited as "002 Tnnn".

## Execution order

Tasks are executed in document order (constitution M11) as a consumer intake (research D1).
Inside a phase, a task is ready when its inputs are delivered; a blocked task does not hold back a
later ready task of the same phase.

## Phase 1: Sources

- [ ] T001 Read through the live library (the `zotero` skill, `health()` first) the definitions
  of research D3, D4, D7 and D8: the Stacks Project definitions of a variety, an algebraic space,
  an algebraic stack and a Deligne–Mumford stack; Kollár–Mori §2.3; Kollár, *Singularities of the
  MMP*, §5; Kollár, *Families of Varieties of General Type*, the chapters on stable families;
  arXiv:2312.03638 §§5, 7. Record each item key, tag and locator in #38 or #39, and run the search
  of constitution M8 for every notion of FR-001–FR-014. A source the library does not hold is
  recorded under LC-05.

## Phase 2: Schemes (US1, #38)

- [ ] T002 [US1] FR-001: register $\mathbf{Sch}_{/S}$ with base change and the morphism properties
  of FR-001 as Mathlib `MorphismProperty`s with their stability theorems. Files:
  `AlgebraicGeometry/Scheme/`, `Catalogue/Semantics/Algebra/Schemes.lean`. Inputs: T001, 001 T023
  (slices and Spec), 001 T046 ($\mathbf{Sch} \to \mathbf{Top}$).
  Check: a new `AlgebraicGeometry/Scheme/MorphismPropertyTests.lean`.
- [ ] T003 [US1] FR-002: varieties by D3, their dimension, and curves and surfaces as values of
  one family of proper varieties; compare `Schemes/Varieties.lean` and
  `AlgebraicGeometry/ClassicalVariety.lean` with D3 and keep one owner. Inputs: T002. Decision: D3.
  Check: $\mathbb P^1_k$ is a curve and $\mathbb P^2_k$ a surface; $\operatorname{Spec} k[x]/(x^2)$
  is not a variety.
- [ ] T004 [US1] FR-003: coherent sheaves, reflexive sheaves as the isomorphism locus of
  $F \to F^{\vee\vee}$ and reflexive powers. Files: `AlgebraicGeometry/Modules/`. Inputs: T002.
  Check: a new `AlgebraicGeometry/Modules/ReflexiveTests.lean`.
- [ ] T005 [US1] FR-003: Weil and Cartier divisors, $\mathbb Q$-divisors, the class group, the
  Picard group, the canonical and dualizing sheaves and the demi-normal data of D4, at the corpus
  owners. Files: `Schemes/Divisors.lean`, `Schemes/WeilDivisorClassGroupData.lean`. Inputs: T004,
  002 T029, 002 T030. Decision: D4. Check: $\operatorname{Cl}(\mathbb P^n_k) \cong \mathbb Z$.
- [ ] T006 [US1] FR-004: the blowup of a scheme along a closed subscheme with its universal
  property. Files: a new `AlgebraicGeometry/Blowup.lean`. Inputs: T002. Check: the blowup of
  $\mathbb A^2_k$ at the origin and its universal property.
- [ ] T007 [US1] FR-004: cyclic covers with their governing algebra and root datum, finite
  quotients with their action, minimal resolutions of rational double points with their
  minimality, and covers and families as arrow-category loci. Files: a new
  `AlgebraicGeometry/Covers.lean`, `AlgebraicGeometry/Blowup.lean`. Inputs: T005, T006. Check:
  the double cover of $\mathbb P^1_k$ branched at two points.

## Phase 3: Stacks (US2, #39)

- [ ] T008 [US2] FR-005: categories fibred in groupoids over $\mathbf{Sch}_{/S}$, descent data,
  prestacks and stacks for the fppf topology. Files: a new `AlgebraicGeometry/Stacks/Basic.lean`.
  Inputs: T002. Decision: D5. Check: the stack of quasi-coherent sheaves satisfies descent.
- [ ] T009 [US2] FR-006: algebraic spaces, algebraic and Deligne–Mumford stacks, representable
  morphisms, diagonals, atlases and the fully faithful chain of FR-006. Files: a new
  `AlgebraicGeometry/Stacks/Algebraic.lean`. Inputs: T008. Decision: D6. Check: a scheme is an
  algebraic space through the embedding; a coarse moduli space is not taken to be a variety.
- [ ] T010 [US2] FR-007: group objects and actions, torsors, $BG$ and $[X/G]$ with their stack
  conditions and the coarse orbit sheaf. Files: a new `AlgebraicGeometry/Stacks/Quotient.lean`.
  Inputs: T009. Check: $[\operatorname{Spec} k / G]$ is $BG$ for a finite group $G$.
- [ ] T011 [US2] FR-008: moduli problems, fine moduli objects and coarse moduli spaces. Files: a
  new `AlgebraicGeometry/Stacks/Moduli.lean`. Inputs: T009. Check: the moduli problem of
  $G$-torsors is the stack $BG$, which has no fine moduli scheme for a nontrivial finite $G$.
- [ ] T012 [US2] FR-009: square-zero extensions, deformation groupoids, the cotangent complex and
  the two deformation problems of D9 through the transitivity triangle. Files: a new
  `AlgebraicGeometry/Deformation.lean`, `CategoryTheory/Deformation.lean`. Inputs: T002.
  Decision: D9. Check: the tangent space of $\operatorname{Spec} k[x]$ at the origin is $k$.

## Phase 4: Pairs and the KSBA stack (US3, #39, #9)

- [ ] T013 [US3] FR-010: log pairs, discrepancies on divisorial valuations, and the classes of
  D7. Files: a new `AlgebraicGeometry/Pairs/Singularities.lean`. Inputs: T005, T006. Decision: D7.
  Check: an $A_1$ surface singularity is canonical; a pair whose $K_X + \Delta$ is not
  $\mathbb Q$-Cartier is refused.
- [ ] T014 [US3] FR-011: stable pairs and stable families with Kollár's condition. Files: a new
  `AlgebraicGeometry/Pairs/Stable.lean`. Inputs: T013. Decision: D7. Check: a smooth curve of
  genus $2$ with $\Delta = 0$ is stable; $\mathbb P^1$ with $\Delta = 0$ is not.
- [ ] T015 [US3] FR-012: the KSBA moduli fibred category and its stack condition. Files: a new
  `AlgebraicGeometry/Pairs/KSBA.lean`. Inputs: T008, T014. Decisions: D2, D8. Check: tier 1 with
  the descent theorem.
- [ ] T016 [US3] FR-013: the Coble instance predicate. Files: `AlgebraicGeometry/Pairs/KSBA.lean`.
  Inputs: T015, T001. Decision: D8. Check: the invariants are those read from the source.

## Phase 5: Stable curves (US4, #39)

- [ ] T017 [P] [US4] FR-014: stable marked graphs, isomorphisms, contractions and the
  specialization poset. Files: a new `Combinatorics/StableGraph.lean`. Check: the four stable
  graphs of $\overline{\mathcal M}_{0,4}$ and their poset.
- [ ] T018 [US4] FR-014: the moduli fibred category $\overline{\mathcal M}_{g,n}$ of stable curves
  and its stack condition; the dual-graph map to the poset of T017. Files: a new
  `AlgebraicGeometry/Stacks/StableCurves.lean`. Inputs: T008, T017. Decision: D2. Check: tier 1.

## Phase 6: Registry and milestone

- [ ] T019 FR-015: registry rows for the categories of this feature with their structural
  functors; update the "Lean realization status" paragraphs of `FOUNDATIONS.md` Part VII that the
  feature changes. Files: `Catalogue/Semantics/Algebra/Schemes.lean`, a new
  `Catalogue/Semantics/Algebra/Stacks.lean`. Inputs: T002–T018. Check:
  `Catalogue/Registry/SnapshotTests.lean` lists the rows.
- [ ] T020 Milestone: every requirement holds, the success-criteria table is measured at the
  milestone revision, and `just test` passes. Performs no other work.

## Dependencies & Execution Order

- T001 first. T002 needs 001 T023 and 001 T046 and precedes Phases 2–5. T005 needs 002 T029 and
  002 T030. T008 before T009–T011, T015, T018.
- T013 needs T005, T006; T014 needs T013; T015 needs T008, T014; T016 needs T015.
- T019 after T002–T018; T020 last.

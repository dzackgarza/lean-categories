# Tasks: The algebraic categories of the catalogue

**Input**: [spec.md](spec.md), [plan.md](plan.md), [research.md](research.md),
[quickstart.md](quickstart.md)

**Tests**: required. Each task's acceptance is assertions in the named test module, through the
registered declarations (constitution E2). Each task applies Contract F of feature 005.

Paths are relative to `LeanCategories/`. `Sem/` is `Catalogue/Semantics/`.

## Format: `[ID] [P?] [Story] Description`

`[P]` marks a task whose drafting can run beside its neighbours; Lean checks run one at a time
(constitution E10). Inputs from other features are cited as "005 Tnnn".

## Execution order

Select issues in definition-first native tree order (constitution M11); within the selected
issue, execute tasks in prerequisite order (research D1). Inside a phase, a task follows the tasks whose results it uses; the workstream does each input task first, in the feature or repository that owns it, and then returns (constitution M11). Each task records its search in its issue first.

## Phase 1: Rings (US1, US2, #55, #102)

- [ ] T001 [US1] #55 FR-001: register integral domains, UFDs with a chosen normalization, PIDs and
  Euclidean domains with their structural functors, the category of elements of the underlying
  set of UFDs and the objects $\mathbb Z$, $\mathbb Z[x]$, $\mathbb Q[x]$, $\mathbb C[x]$. Files:
  a new `Sem/Algebra/DivisibilityTower.lean`, `Algebra/Euclidean.lean`. Decision: D2. Acceptance
  in a new `Sem/Algebra/DivisibilityTowerTests.lean`: $\mathbb Z$ reaches UFDs through the
  functors; $\mathbb Z[x]$ is a UFD and is refused as a PID by $(2, x)$.
- [ ] T002 [US2] #102 FR-004: the quotient $R/I$ as a constructor with its universal property and
  the round trip $I \mapsto \ker(R \to R/I)$; fractional ideals as $R$-submodules of
  $\operatorname{Frac}(R)$ with their product and invertibility. Files: `Algebra/{Ideals,FractionalIdeals}.lean`,
  `Sem/Modules/Operations.lean`. Acceptance in a new `Sem/Algebra/RingConstructionTests.lean`:
  $\mathbb Z/(2)$ has the universal property; $\tfrac12\mathbb Z$ is invertible with inverse
  $2\mathbb Z$.
- [ ] T003 [US2] #102 FR-004: localization of rings and modules with their universal properties,
  the $I$-adic completion functor and the regular-module section. Files: a new
  `Sem/Algebra/Localization.lean`, `Sem/Modules/CatalogueRegistration.lean`. Acceptance in
  `Sem/Algebra/RingConstructionTests.lean`: $\mathbb Z_{(p)}$ is the localization at $p$; $\mathbb Z$
  is an object of $\operatorname{Mod}(\mathbb Z)$ through the section.

## Phase 2: Modules (US5, #101)

- [ ] T004 [US5] #101 FR-002: certified free-plus-torsion modules over an integral domain with the
  forgetful functor and direct sums. Files: a new `Modules/FreeTorsionSplitting.lean`. Decision:
  D3. Acceptance in a new `Modules/FreeTorsionSplittingTests.lean`: $\mathbb Z^2 \oplus \mathbb Z/6$
  is certified; the ideal $(2, 1 + \sqrt{-5})$ of $\mathbb Z[\sqrt{-5}]$ has no certificate with
  $T = 0$.
- [ ] T005 [US5] #101 FR-003: the theorem of each operation of FR-003 with its hypotheses and
  output splitting. Files: `Modules/FreeTorsionSplitting.lean`. Inputs: T004. Acceptance in
  `Modules/FreeTorsionSplittingTests.lean`: over a PID kernels and cokernels of maps of finitely
  generated modules return splittings; over $\mathbb Z[\sqrt{-5}]$ a kernel without one is exhibited.

## Phase 3: Groups (US3, #103, #104, #106)

- [ ] T006 [US3] #103 FR-005: groups and abelian groups, $G$-sets with their permutation
  representations, presented groups with their comparison maps, and $\operatorname{Aut}_{\mathcal C}$
  through the generic construction of feature 001 FR-051. Files: `Algebra/GroupTheory.lean`, a new
  `Sem/Algebra/GroupActions.lean`. Inputs: 001 T086. Acceptance in a new
  `Sem/Algebra/GroupTests.lean`: the permutation representation of $\mathbf{Sym}(3)$ on
  $\{1, 2, 3\}$; $\langle a \mid a^n \rangle \cong \mathbb Z/n$.
- [ ] T007 [US3] #103 FR-005: invariant factors of finite abelian groups as an invariant on the core
  with the chosen decomposition. Files: `Algebra/FiniteAbelian.lean`. Decision: D4. Acceptance in
  `Sem/Algebra/GroupTests.lean`: $\mathbb Z/4 \times \mathbb Z/6$ has invariant factors $(2, 12)$.
- [ ] T008 [US3] #104 FR-006: $G$-modules, invariants, coinvariants, their adjunctions and the
  saturation theorem. Files: a new `Modules/GroupModules.lean`. Decision: D5. Acceptance in a new
  `Modules/GroupModulesTests.lean`: the swap on $\mathbb Z^2$ has invariants the diagonal and
  coinvariants $\mathbb Z$.
- [ ] T009 [US3] #106 FR-007: finitely generated groups, the subgroup constructions, the Schreier
  theorem and generating families as `choice` operations. Files: `Algebra/GroupGeneration.lean`,
  `Sem/Algebra/GroupActions.lean`. Inputs: 001 T037. Acceptance in `Sem/Algebra/GroupTests.lean`:
  the commutator subgroup of the free group on two letters is not finitely generated; an index-$2$
  subgroup of that free group is free of rank $3$.

## Phase 4: Complexes and algebras (US4, #107, #108)

- [ ] T010 [US4] #107 FR-008: register the category of chain complexes of $R$-modules, chain maps,
  homotopies, cones, shifts, truncations, tensor and Hom complexes, the homology functors and the
  long exact sequence at their FC05 owners. Files: `Homological/`, a new
  `Sem/Modules/Complexes.lean`. Decision: D6. Acceptance in a new `Sem/Modules/ComplexesTests.lean`:
  a differential with $d^2 \neq 0$ is refused; the sequence of $0 \to \mathbb Z \xrightarrow{2} \mathbb Z \to \mathbb Z/2 \to 0$.
- [ ] T011 [US4] #107 FR-008: register singular, group, sheaf and de Rham cohomology as composites
  through complexes and homology, at their corpus owners. Files: `Sem/Modules/Complexes.lean`.
  Inputs: T010. Acceptance in `Sem/Modules/ComplexesTests.lean`: each cohomology row is a composite
  that names the homology functor.
- [ ] T012 [US4] #108 FR-009: graded and differential graded algebras, Lie algebras, Clifford and
  exterior algebras and the cohomology ring. Files: `Algebra/GradedAntiderivation.lean`, a new
  `Sem/Algebra/GradedAlgebras.lean`. Inputs: 005 T017. Decision: D7. Acceptance in a new
  `Sem/Algebra/GradedAlgebrasTests.lean`: the Clifford algebra of $x^2 + y^2$ over $\mathbb R$ has
  its universal property; a degree-zero differential is refused.

## Phase 5: Registry and milestone

- [ ] T013 FR-010: every category of this feature has its registry row with its structural
  functors; update the FOUNDATIONS "Lean realization status" paragraphs that the feature changes.
  Inputs: T001–T012. Acceptance in `Catalogue/Registry/SnapshotTests.lean`: the rows are listed and
  reach `cat.sets`.
- [ ] T014 Milestone: every requirement holds, the success-criteria table is measured at the
  milestone revision, and `just test` passes. Performs no other work.

## Dependencies & Execution Order

- T001 first (001 T068 takes it at once). T004 before T005. T006 needs 001 T086; T009 needs
  001 T037; T012 needs 005 T017. T013 after T001–T012; T014 last.

# Tasks: Manifolds, Hodge theory and period constructions

**Input**: [spec.md](spec.md), [plan.md](plan.md), [research.md](research.md),
[quickstart.md](quickstart.md)

**Tests**: each task's check is the tier-1 elaboration of its modules and the theorems it names;
the milestone runs `just test`. Each task applies Contract O of feature 003.

Paths are relative to `LeanCategories/`.

## Format: `[ID] [P?] [Story] Description`

`[P]` marks a task whose drafting can run beside its neighbours; Lean checks run one at a time
(constitution E10). Inputs from other features are cited as "002 Tnnn", "003 Tnnn", "006 Tnnn"
and "007 Tnnn".

## Execution order

Tasks are executed in document order (constitution M11) as a consumer intake (research D1). Inside
a phase, a task follows the tasks whose results it uses; the workstream does each input task first, in the feature or repository that owns it, and then returns (constitution M11).

## Phase 1: Sources

- [ ] T001 Read through the live library the statements of research D4–D9: Carlson–Müller-Stach–Peters
  on variations of Hodge structure; arXiv:1607.05984; Dolgachev–Kondō, arXiv:1201.6093;
  Looijenga, arXiv:math/0201218v2; the Kulikov and integral-affine sources of
  [FOUNDATIONS.md](../../FOUNDATIONS.md) §62; Shioda, *On the Mordell–Weil lattices*. Record each
  item key and locator in #40 or #109, and run the search of constitution M8 for every notion of
  FR-001–FR-014. A source that the library does not hold is added to it first (002 research D16).

## Phase 2: Period domains and quotients (US1, #40)

- [ ] T002 [US1] FR-001: $\Omega_T$ as a complex manifold with its two components, the holomorphic
  action of $O(T_{\mathbb R})$ and $O^+(T)$. Files: `Lattices/Valued/PeriodDomainData.lean`, a new
  `Geometry/TypeIVDomain.lean`. Inputs: T001, 003 T037, 002 T124. Decision: D2. Check: for
  $T = U \perp U$ the domain is biholomorphic to $\mathbb H \times \mathbb H$ on a component.
- [ ] T003 [US1] FR-002: arithmetic subgroups, the quotient stack $[\Omega_T/\Gamma]$ over complex
  analytic spaces and the coarse quotient. Files: a new `Analytic/ArithmeticQuotient.lean`.
  Inputs: T002, 002 T125. Decision: D3. Check: a point with nontrivial stabilizer keeps it in the
  stack and loses it in the coarse quotient.
- [ ] T004 [P] [US1] FR-003: Heegner divisors with their labels. Files:
  `Analytic/ArithmeticQuotient.lean`. Inputs: T003. Check: the divisor of a $(-2)$-vector is the
  image of its hyperplane section.

## Phase 3: Variations and period maps (US2, #40, #9)

- [ ] T005 [US2] FR-004: local systems, the monodromy representation and markings. Files: a new
  `Topology/LocalSystem.lean`. Inputs: T001, 002 T124. Check: the local system of a covering of
  the circle and its monodromy.
- [ ] T006 [US2] FR-005: polarized variations of Hodge structure. Files: a new
  `Geometry/VariationOfHodgeStructure.lean`. Inputs: T005, 003 T036, 002 T043. Decision: D4.
  Check: the constant variation and the variation over $\Omega_T$ of 002 T043.
- [ ] T007 [US2] FR-006: the period map as a morphism of stacks, its marked form and its
  functoriality under base change; the worked example of arXiv:1607.05984. Files: a new
  `Geometry/PeriodMap.lean`. Inputs: T003, T006, 007 T011. Decision: D5. Check: the period map of
  a pulled-back family is the composite.
- [ ] T008 [US2] FR-007: $T_{\mathrm{Co}}$, $\Gamma_{\mathrm{Co}}$ and the Coble period target.
  Files: `Geometry/PeriodMap.lean`, `Lattices/Valued/` (the lattice owner). Inputs: T001, T007.
  Decision: D6. Check: the signature of $T_{\mathrm{Co}}$ is the one of the source.

## Phase 4: Compactifications (US3, #40, #9)

- [ ] T009 [US3] FR-008: rational boundary components, the cusp poset and the Baily–Borel
  compactification as the Proj of modular forms. Files: a new `Analytic/BailyBorel.lean`. Inputs:
  T003. Decision: D7. Check: the $0$-dimensional cusps of $O^+(U \perp U \perp E_8)$.
- [ ] T010 [US3] FR-009: toroidal compactification data. Files: a new `Analytic/Toroidal.lean`.
  Inputs: T009, 006 T006. Check: the datum of the Coxeter fan at a $0$-dimensional cusp.
- [ ] T011 [US3] FR-010: semifans and semitoroidal compactifications from the source of D8. Files:
  `Analytic/Toroidal.lean`, `Lattices/Valued/SemifanArrangement.lean`. Inputs: T010, 002 T117.
  Decision: D8. Check: a semifan of the source satisfies the axiom list; no declaration identifies
  the restriction to a Heegner divisor with the divisor's own compactification.

## Phase 5: Degenerations (US4, #40, #9)

- [ ] T012 [US4] FR-011: Kulikov degenerations, monodromy, its logarithm and the type. Files: a new
  `Geometry/KulikovDegeneration.lean`. Inputs: T005, 002 T125, 007 T002. Check: the Type III
  logarithm of the spec satisfies $N^3 = 0 \neq N^2$.
- [ ] T013 [US4] FR-012: the integral-affine dual complex of a Type III degeneration. Files:
  `Geometry/KulikovDegeneration.lean`. Inputs: T012, 002 T124. Check: the dual complex is a
  triangulated sphere with an integral-affine structure off its singular points.

## Phase 6: Lattices from varieties (US5, #109)

- [ ] T014 [US5] FR-013: $H^2/\mathrm{torsion}$ with the cup form, $\operatorname{NS}$,
  $\operatorname{Pic}$, the cycle class map, the transcendental lattice, the Hodge decomposition
  and the Hodge isometry of an automorphism, with the examples of D9. Files: a new
  `Geometry/SurfaceLattices.lean`. Inputs: T001, 007 T005, 002 T044, 002 T049, 003 T036.
  Decision: D9. Check: $\mathbb P^1 \times \mathbb P^1$ gives $U$ and the swap acts by exchange;
  $\operatorname{Bl}_k \mathbb P^2$ gives $I_{1,k}$.
- [ ] T015 [US5] FR-014: Mordell–Weil lattices by Shioda's height pairing with the rational
  elliptic surface of D9. Files: `Geometry/SurfaceLattices.lean`. Inputs: T014. Decision: D9.
  Check: the Mordell–Weil lattice of the example is $E_8(-1)$.

## Phase 7: Registry and milestone

- [ ] T016 FR-015: registry rows for the categories of this feature; update the "Lean realization
  status" paragraphs of `FOUNDATIONS.md` §§61–62 that the feature changes. Files: a new
  `Catalogue/Semantics/Geometry/` owner. Inputs: T002–T015. Check:
  `Catalogue/Registry/SnapshotTests.lean` lists the rows.
- [ ] T017 Milestone: every requirement holds, the success-criteria table is measured at the
  milestone revision, and `just test` passes. Performs no other work.

## Dependencies & Execution Order

- T001 first. T002 needs 003 T037, 002 T124; T003 needs 002 T125. T006 needs 003 T036, 002 T043.
- T007 needs T003, T006, 007 T011; T010 needs 006 T006; T011 needs 002 T117.
- T014 needs 007 T005, 002 T044, 002 T049, 003 T036. T016 after T002–T015; T017 last.

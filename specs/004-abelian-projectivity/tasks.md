# Tasks: Abelian projectivity for polarized complex tori

**Input**: [spec.md](spec.md), [plan.md](plan.md), [research.md](research.md),
[quickstart.md](quickstart.md)

**Tests**: each task's check is the tier-1 elaboration of its modules and the theorems it names;
the milestone runs `just test`.

## Format: `[ID] [P?] [Story] Description`

`[P]` marks a task whose drafting can run beside its neighbours. Lean checks run one at a time
(constitution E10). Each task applies Contract O of feature 003.

## Execution order

This task list is executed as task T111 of feature 002 (research D2), in document order
(constitution M11). Inputs from other features are cited as "002 Tnnn" and "003 Tnnn".

## Phase 1: Sources (all stories)

- [ ] T001 Read through the live library (the `zotero` skill, `health()` first) the statements of
  research D4: Appell–Humbert, the canonical theta functions, $h^0 = \operatorname{Pf}(E)$, the
  Lefschetz theorem and Chow's theorem; record each item key and page locator in research.md D4, and
  read FC11-C16-U026–U032 and FC12-C05-U009–U011 at their catalogue rows and admitted sources. A
  source that the library does not hold is recorded under LC-05. Decision: D3, D4.

## Phase 2: Line bundles and Picard data (US1)

- [ ] T002 [US1] Holomorphic line bundles on a complex manifold: the owner of research D5 with
  morphisms, tensor product, dual, pullback, the $\mathbb C$-vector space of holomorphic sections and
  $\operatorname{Pic}(X)$ as the group of isomorphism classes; one positive and one separating example
  (a nontrivial bundle with no nonzero section). Files: new owner under `LeanCategories/Geometry/`.
  Inputs: T001. Decision: D5.
- [ ] T003 [US1] Complex projective space as a complex manifold, its hyperplane bundle $\mathcal O(1)$
  with $H^0 = (\mathbb C^{N+1})^\vee$, closed holomorphic embeddings, and the map to
  $\mathbb P(H^0(X, L)^\vee)$ of a base-point-free bundle. Inputs: T002.

## Phase 3: Appell–Humbert (US2)

- [ ] T004 [US2] On $T = V/\Gamma$: the group $\mathcal P(\Gamma)$ of pairs $(H, \alpha)$, the line
  bundle $L(H, \alpha)$ of the canonical factor of automorphy, the comparison of factors of automorphy
  with line bundles on $T$, the Appell–Humbert isomorphism $\mathcal P(\Gamma) \cong \operatorname{Pic}(T)$
  and the exact sequence $0 \to \operatorname{Pic}^0 \to \operatorname{Pic} \to \operatorname{NS} \to 0$.
  Files: `Lattices/Valued/ComplexTorus.lean` and the T002 owner. Inputs: T002, 003 T037.
- [ ] T005 [US2] The comparison of `IsAbelianVariety` with the existence of a positive definite $H$ in
  $\operatorname{NS}(T)$ ($H(x, y) = E(ix, y) + iE(x, y)$), and with the weight-one polarized Hodge
  structure of 003 T036. Inputs: T004, 003 T036.

## Phase 4: Theta sections and the embedding (US3)

- [ ] T006 [US3] The canonical theta functions as $H^0(T, L(H, \alpha))$ and
  $h^0 = \operatorname{Pf}(E)$ for positive definite $H$, consuming the FC11-C16 owners. Inputs: T004.
- [ ] T007 [US3] The Lefschetz theorem: $L^{\otimes 2}$ is base-point free and $L^{\otimes 3}$ very
  ample for positive definite $H$; the sections of $L^{\otimes 3}$ give a closed holomorphic embedding
  $T \hookrightarrow \mathbb P^N(\mathbb C)$, $N = 3^g \operatorname{Pf}(E) - 1$. Inputs: T003, T006.

## Phase 5: The algebraic variety (US4)

- [ ] T008 [US4] Chow's theorem: a closed analytic subset of $\mathbb P^N(\mathbb C)$ is the zero set of
  finitely many homogeneous polynomials. Inputs: T003, 002 T125. Decision: D6.
- [ ] T009 [US4] The final theorem: a complex torus with a Riemann form is isomorphic, as a complex
  manifold, to $X(\mathbb C)$ for a projective variety $X$ over $\mathbb C$ (`IsProjectiveVariety`);
  compare with FC12-C05-U009 at its 002 owner. Inputs: T005, T007, T008. Decisions: D1, D6.
- [ ] T010 Milestone: the four success criteria of the plan hold, the spec's table is measured at
  the milestone revision, and `just test` passes. Performs no other work.

## Dependencies & Execution Order

- T001 before every task; Phase 2 before Phase 3; T004 before T005 and T006; T003 and T006 before
  T007; T003 and 002 T125 before T008; T005, T007, T008 before T009.
- External inputs: 003 T036, T037; 002 T125.

## Implementation Strategy

Phases 2–5 in order; each phase is an increment that a mathematician can use (line bundles, then
the classification, then the embedding, then the variety).

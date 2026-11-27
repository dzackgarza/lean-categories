# Tasks: Classifier foundation, proof-carrying registry and catalogue release

**Input**: [spec.md](spec.md), [plan.md](plan.md), [research.md](research.md),
[data-model.md](data-model.md), [quickstart.md](quickstart.md)

**Tests**: required. Each task's acceptance is assertions in the named test module, through the
registered declarations (constitution E2). Each task applies plan.md Contract F.

Paths are relative to `LeanCategories/`, except `README.md`, `FOUNDATIONS.md`, `justfile`,
`scripts/` and `Integration/` at the repository root. `Reg/` is `Catalogue/Registry/`. `Sem/` is
`Catalogue/Semantics/`.

## Format: `[ID] [P?] [Story] Description`

`[P]` marks a task whose drafting can run beside its neighbours; Lean checks run one at a time
(constitution E10). Inputs from other features are cited as "001 Tnnn".

## Execution order

Use the [repository-wide Spec Kit execution order](../002-foundational-corpus-sweeps/tasks.md#repository-wide-execution-order)
under constitution M11. The task IDs here are the implementation units and their checkboxes
own completion. The phase headings group related requirements, not a competing scheduler.
Do the exact prerequisites of the selected task first, in their owning features. Definitions
precede independent proof work, including across features. Each task records its search at its issue first (Contract F).

## Phase 1: Classifiers (US1, #30)

- [ ] T001 [US1] FR-001, FR-002: give the classifier an ambient-model interface with the strict
  2-category of Mathlib categories as its realization (`data-model.md` `Classifier.model`);
  make `PropertyClassifier` the abbreviation over `Classifier` with `full`, `faithful` and
  `replete` (`data-model.md` `PropertyClassifier.replete`), and prove that
  `Classifier.ofProperty P` is one; state property, structure and stuff as cumulative classes
  of the classifying fibre. Files: `CategoryTheory/OneCat/{Universes,Classifier}.lean`.
  Decisions: D1, D2. Acceptance in a new `CategoryTheory/OneCat/ClassifierTests.lean`: the
  commutativity classifier of magmas is a property classifier; the forgetful functor of unital
  magmas with inverse is faithful and not full (the counterexample of D3).
- [ ] T002 [US1] FR-003: prove the universal property of `reindex` from Mathlib
  `CategoricalPullback.functorEquiv`, the identity and composition equivalences as theorems in
  place of the structures `ReindexIdIso`, `ReindexCompIso`, and pullback pasting; add
  `ClassifierSquare` with its actual `CatCommSq` (`data-model.md` `ClassifierSquare.iso`) and
  its composition. Files: `CategoryTheory/OneCat/{Reindex,CategoricalPullback}.lean`.
  Acceptance in a new `CategoryTheory/OneCat/ReindexTests.lean`: reindexing commutativity of
  magmas along groups gives commutative groups by a proved equivalence; the composite square's
  2-cell is the pasting of its two 2-cells.
- [ ] T003 [US1] FR-004: declare the arrow and diagram objects,
  $\operatorname{Op}_n(\mathcal E)$, the diagram-extension classifier of a boundary-extension
  datum and the operadic matching hook with its named $A_\infty$ model, instantiated by
  associativity and its pentagon. Files: new
  `CategoryTheory/OneCat/{OperationClassifier,DiagramExtension,OperadicMatching}.lean`. Decision:
  D4. Acceptance in a new `CategoryTheory/OneCat/OperationClassifierTests.lean`:
  $\operatorname{Op}_2(\mathbf{Set})$ is equivalent to `MagmaCat`; the associativity extension
  classifier over it is equivalent to `Semigrp`.
- [ ] T004 [US1] FR-005: prove $\operatorname{Alg}_{E_1}(\mathbf{Set}) \simeq \mathbf{Mon}$ through
  `monTypeEquivalenceMon` and the pseudomonoid case with strong monoidal 1-morphisms; prove the
  role components equivalent to `MagmaCat`; build the two-operation pullback over
  $\mathbf{Set}$ and rings as its iterated refinement; host the inverse classifier on monoids and
  prove $\mathbf{Grp} \to \mathbf{Mon}$ fully faithful. Files:
  `Algebra/Concrete/Magmas.lean`, `CategoryTheory/OneCat/Classifier.lean`. Decisions: D3, D5.
  Acceptance in a new `Algebra/Concrete/GroundingTests.lean`: the two equivalences elaborate;
  an involutive unary operation on a monoid that is not an inverse is refused as a group.
- [ ] T005 [US1] FR-006: refuse a second classifier row with the same classifier and host; record
  the fourteen collisions of #30 as fixtures; define the lattice-poset classifiers of #30 from
  their operations. Files: `Reg/Semantic.lean`. Acceptance in a new
  `Reg/ClassifierIdentityTests.lean`: each fixture registers once and its second spelling is an
  alias; a duplicate is refused.

## Phase 2: The proof-carrying registry (US2, #31, #4)

- [ ] T006 [US2] FR-007: add the denotation witness to every category and functor row
  (`data-model.md` category and functor rows `denotation`) and a generic evaluator of the
  expression language with no identifier case split; constructor expressions evaluate; endpoints
  are compared by equivalence. Files: `Catalogue/{Syntax,Interpretation,Realization}.lean`,
  `Reg/Entry.lean`, `Reg/Semantic.lean`. Acceptance in a new `Reg/InterpretationTests.lean`:
  every row of the snapshot evaluates with its witness; the expression of graded finite rings
  evaluates (#4, transferred requirement 1).
- [ ] T007 [US2] FR-008: `canonicalize` with its rewrite certificate under proved termination and
  confluence, non-committal otherwise; chosen hosts as initial objects or named sections;
  refusal of alias cycles and of dangling references, which end the structural projection.
  Files: `Reg/Semantic.lean`, `Catalogue/Syntax.lean`. Acceptance in
  `Reg/InterpretationTests.lean`: a dangling reference is refused at registration and a
  projection through it stops with no route.
- [ ] T008 [US2] FR-009: add 2-cell, diagram, filler, equivalence and operadic-algebra
  expressions (`data-model.md` `CategoryExpr` constructors) with their evaluation relative to a
  realization. Files: `Catalogue/{Syntax,Interpretation}.lean`. Acceptance in
  `Reg/InterpretationTests.lean`: the pentagon of T003 is a filler expression that evaluates.
- [ ] T009 [US2] FR-010: validate at registration the declaration, the host, the family
  parameters and variance, the functor endpoints, the transport policy, the aliases and the
  presentation equivalences; record the total and the leg of each classifier row
  (`data-model.md` `ClassifierEntry.total`, `.leg`); register `clf.division` by reindexing along
  rings to the two-operation category (#4, transferred requirement 3); put the presentation
  equivalences in the snapshot. Files: `Reg/{Entry,Semantic,Snapshot}.lean`. Acceptance in
  `Reg/SnapshotTests.lean`: a consumer rebuilds the pullback of a refinement from the snapshot
  alone; a classifier row with no leg is refused.

## Phase 3: Constructors and families (US3, #54)

- [ ] T010 [US3] FR-011: give every constructor its typed declaration (`data-model.md`
  `ConstructorEntry.parameters`, `.hypotheses`, `.onMorphisms`, `.evaluator`); express
  $\operatorname{Subobjects}(\mathbf{Set})$, slices, coslices, arrow categories and categories of
  elements as generic constructor values; keep $\operatorname{Aut}_{\mathcal C}(X)$ a value of a
  generic assignment. Inputs: 001 T035, 001 T086. Files: `Catalogue/Constructors.lean`,
  `Sem/ConstructorRegistration.lean`, `Reg/Entry.lean`. Acceptance in a new
  `Reg/ConstructorTests.lean`: each example elaborates through the generic constructor and its
  export reconstructs it; the coslice of `Cat` at the point is not a compatibility host.
- [ ] T011 [US3] FR-012: declare the families of FR-012 as Grothendieck constructions with typed
  parameters and variance (`data-model.md` `CategoryFamilyEntry.base`, `.variance`,
  `.fibration`), the comparison of left $R$-modules with $\operatorname{Bimodules}(R, \mathbb Z)$,
  and the convention of $\operatorname{Modules}(R)$. Inputs: 001 T056. Files:
  `Catalogue/FamilyFibration.lean`, `Sem/Modules/CatalogueRegistration.lean`,
  `Sem/FibrationRegistration.lean`. Decisions: D6, D7. Acceptance in a new
  `Sem/Modules/FamilyTests.lean`: $\operatorname{VectorSpaces}(\mathbb C)$ and
  $\operatorname{Bimodules}(\mathbb C, \mathbb C)$ are distinct applications;
  $\operatorname{VectorSpaces}(\mathbb Q)$ projects to the left modules over $\mathbb Q$.
- [ ] T012 [US3] FR-013: resolve composed and refined heads at their exact host; the five
  fixtures of #54 (`Cellular`, `Stratified`, `Supercocommutative`, `Supercommutative`,
  `WellGenerated`) resolve or report the named missing declaration. Files: `Reg/Semantic.lean`.
  Acceptance in `Reg/ConstructorTests.lean`: finite-dimensional vector spaces over $K$ resolve to
  the finite-rank classifier on $\operatorname{VectorSpaces}(K)$; a weaker host is refused.

## Phase 4: Operations and methods (US4, #28, #53)

- [ ] T013 [US4] FR-014: register $\operatorname{card}$ on $\operatorname{Core}(\mathbf{Set})$ as
  the one cardinality with its finite restriction, index on arrow-category objects, the
  bitorsor of $\operatorname{Isom}_{\mathcal C}(X, Y)$ with both transporters, the
  underlying-object functors, commutativity as a functor on cores and `is_abelian` as its
  composite. Inputs: 001 T005. Files: `Sem/Foundation/Cardinality.lean`,
  `Sem/Algebra/Automorphisms.lean`, `Sem/Algebra/Catalogue/Magmas.lean`. Acceptance in a new
  `Sem/OperationTests.lean`: $|(\mathbb Z/2)^4| = 16$ through the route from modules; the domain
  transporter satisfies $\sigma \circ (\sigma^{-1} \circ \tau) = \tau$; additive and
  multiplicative commutativity of a ring are distinct rows.
- [ ] T014 [US4] FR-015: make the method row name a normalized functor expression
  (`data-model.md` `MethodEntry.semantic`); refuse a row that does not typecheck; inherit only
  along structural functors; record the cells that relate parallel routes. Files:
  `Reg/{Entry,Semantic}.lean`. Decisions: D8, D9. Acceptance in `Sem/OperationTests.lean`: the
  free functor from sets to commutative rings grants no `factor`; two routes related by a
  registered cell carry that cell.

## Phase 5: The standard vocabulary (US5, #41)

- [ ] T015 [US5] FR-016: register adjunctions with unit, counit and triangle identities
  (`data-model.md` `AdjunctionEntry.unit`, `.counit`, `.triangles`), free objects as initial
  objects of comma categories, essential-image factorizations, restriction and corestriction,
  and mates, over Mathlib `Adjunction`, `StructuredArrow`, `Functor.toEssImage` and `mateEquiv`.
  Files: `Reg/Entry.lean`, a new `Sem/Vocabulary/Adjunctions.lean`. Acceptance in a new
  `Sem/Vocabulary/VocabularyTests.lean`: the free–forgetful adjunction of modules satisfies its
  triangle identities; the essential image of a fully faithful functor is replete.
- [ ] T016 [US5] FR-016: register reflective and coreflective localizations with recognition by
  the unit (`data-model.md` `ReflectiveLocalizationEntry.recognition`), sheafification as the
  reflective localization of Mathlib, and stackification ([FOUNDATIONS.md](../../FOUNDATIONS.md)
  Thm. 31.5). Files: a new `Sem/Vocabulary/Localizations.lean`, `CategoryTheory/Sites/`.
  Acceptance in `Sem/Vocabulary/VocabularyTests.lean`: a presheaf is a sheaf exactly when the
  unit at it is an isomorphism.
- [ ] T017 [US5] FR-016: register the free-algebra catalogue (free monoid, group, abelian group,
  module, tensor algebra, free associative and commutative algebra, symmetric algebra, free
  operadic algebra), the monoid-algebra functor with the group-like adjunction and the
  recognition theorem of its essential image under the connected-base hypothesis, and the
  free-module functor as a strong symmetric monoidal functor. Files: `Algebra/FreeAlgebras.lean`,
  a new `Sem/Vocabulary/FreeAlgebras.lean`. Acceptance in `Sem/Vocabulary/VocabularyTests.lean`:
  the group algebra of $\mathbb Z/2$ over $\mathbb Q$ is recognized; a basis condition alone is
  refused as a definition of a monoid algebra.
- [ ] T018 FR-017: fold Amendments 18.1–18.6 of the first addendum of `FOUNDATIONS.md` into the
  places they name and delete the amendment list; the mathematics is unchanged
  (constitution M10). File: `FOUNDATIONS.md`. Acceptance: each amendment's content is at its
  named place, read against the amendment text.
  In the same change, replace the status sentence of §13 (before Definition 13.10) that names
  issue #62 as an open obligation: #62 is complete, and the general owner is
  `AugmentedGradedObject` (`LeanCategories/Modules/AugmentedObjects.lean`); state, from the
  source, which specialization and forgetful functors from it to the free covers, based modules
  and coordinates of `LeanCategories/Modules/TruncatedResolutions.lean` exist, and give each
  missing one its task in this feature.

## Phase 6: Vertical slices (US6, #29)

- [ ] T019 [US6] FR-018: the $\mathbb F_2^2$ slice and the $A_2$ slice through registered rows
  only. Inputs: T013. Files: a new `Sem/VerticalSliceTests.lean`. Acceptance: $|M| = 4$; the
  numbering and `nth` table of $M$; $\det G$ at the chosen frame; the radical and the isotropic
  vectors of $G$; $\det = 3$ and $|A_{A_2}| = 3$; a second Gram matrix $P^{\mathsf T} G P$ is an
  isometric object, not an equal one.

## Phase 7: Export and releases (US7, #4, #50, #51)

- [ ] T020 [US7] FR-019: generate the JSON and semantic DOT of D11 from `RegistrySnapshot`
  (`data-model.md` `ReleaseManifest.schemaVersion`, `.tag`, `.revision`, `.rows`) with a `just`
  recipe that reproduces them from a clean checkout; state the stable-ID policy of D10 in
  `README.md`. Files: a new `Tools/RegistryExport.lean`, `justfile`, `README.md`. Decisions:
  D10–D12. Acceptance: two runs on one revision give identical files; every edge has a kind.
- [ ] T021 FR-020: replace the README source tree by the current one; name
  `Catalogue/Syntax.lean`, `Catalogue/Registry/{Entry,Extension}.lean`,
  `Catalogue/{Interpretation,Realization}.lean` and the structural routes of
  `Catalogue/Registry/{Semantic,RouteDiscovery}.lean` in #53 §17; replace the README sentence
  that names the issue ledger as the execution state by the Spec Kit task lists (constitution
  M11). Files: `README.md`, the body of #53. Acceptance: every path in both resolves; the
  COMPLAINTS.md entry "README tree and issue #53 cite registry paths that no longer exist"
  closes with its evidence.
- [ ] T022 [US7] FR-021: cut the Foundation 0.1 release tag at a revision where T001–T021 and
  001 T042 hold and `just test` passes; record the tag and its export in #50. Inputs: T001–T021,
  001 T042. Decision: D13. Acceptance: `Integration/RegistryConsumer/` builds against the tag.
- [ ] T023 [US7] FR-021: cut the Lattice arithmetic 0.2 release tag at a revision where 003 T009
  and 003 T034 hold and `just test` passes; record it in #51. Inputs: T020, 003 T009, 003 T034.
  Decision: D13. Acceptance: the release export holds the rows of 003 N04, N05, N09 and N21.

## Phase 8: Certification, publication, milestone (US7, #4, #59)

- [ ] T024 [US7] FR-022: certify the complete catalogue: compute the generating diagram and its
  closure from the reflected registry and write the coverage report against the categories that
  FOUNDATIONS and the specifications of 001, 003 and 005–009 require; every missing category is
  a task of its owning feature before this task closes. Inputs: 001 T042, 003 T049, 006 T014,
  007 T020, 008 T017, 009 T014. Decision: D14. Acceptance: the report lists 0 required
  categories without a row.
- [ ] T025 [US7] FR-023: publish every definition module and card to Prove2Me with
  `scripts/publish_prove2me.py`: dry run, private run, then public run; the recipe selects the
  platform environment at publication and builds in a scratch checkout. Inputs: T024. Decision:
  D15. Acceptance: a rerun on an unchanged repository submits nothing; a probe theorem that
  imports a published definition compiles on the platform.
- [ ] T026 Milestone: `just test` passes on `main` with all tasks above landed; the spec's
  success-criteria table is measured at that revision. Performs no other work.

## Dependencies & Execution Order

- Phase 1 comes before Phase 2 (rows evaluate classifier totals). Phase 2 comes before Phases 3 and 4.
- T010 needs 001 T035 and 001 T086; T011 needs 001 T056; T013 needs 001 T005; T019 needs T013.
- T022 needs T001–T021 and 001 T042; T023 needs 003 T009 and 003 T034.
- T024 needs the milestones of 001, 003 and 006–009; T025 needs T024.

## Implementation Strategy

1. Phases 1–2: the classifier and the proof-carrying registry (MVP for US1, US2).
2. Phases 3–6: constructors, families, operations, vocabulary and slices.
3. Phase 7: the export and the two releases.
4. Phase 8: certification and publication.

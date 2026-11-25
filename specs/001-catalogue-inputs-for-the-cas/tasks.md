# Tasks: Catalogue inputs for the computer-algebra roadmap

**Input**: [spec.md](spec.md), [plan.md](plan.md), [research.md](research.md),
[data-model.md](data-model.md), [contracts/registry-additions.md](contracts/registry-additions.md)

**Tests**: required. Each task's acceptance is assertions in the named test module, through the
registered declarations (constitution E2).

Paths are relative to `LeanCategories/`, except `justfile`, `scripts/` and `.gitignore` at the
repository root. `Sem/` is `Catalogue/Semantics/`. `Reg/` is `Catalogue/Registry/`.

## Format: `[ID] [P?] [Story] Description`

Each task names its issue, its files, its acceptance and the kernel task that it unblocks (the
lean-cas-dsl task list, "Upstream inputs recorded as missing").

## Execution order

Tasks are executed in document order. The issue phases follow the document order of their first
consumers in the kernel task list: T131, T138, T121, T119, T129, T122, T132, T120, T125, T136,
T124, T128, T130, T123, T135, T134, T118, T137, T133. Within an issue, the search task comes
before the declaration task. Every declaration task also passes tier 1 at each change, adds its
new modules to `LeanCategories/All.lean`, and is reviewed by an author who did not write it
(constitution M10). A task closes its issue when its acceptance holds on `main`.

## Phase 1: Setup (fast feedback, logs and timing)

- [ ] T001 Add the private tier-1 recipe `loop` to `justfile`: `just loop <module> [modules]`
  elaborates each module with `flock .tmp/lean.lock lake env lean`, in order, and stops at the
  first error. Constitution E1, E4. Acceptance: `just loop LeanCategories/Catalogue/Registry/OperationBindingTests.lean`
  finishes under 300 s on the research image with the shared cache. Unblocks: every later task.
- [ ] T002 Make `just loop` and `just test` write a durable log of each run to `build-logs/<commit>-<start time>.log`
  in the repository tree, through `scripts/build-timing.sh`. Constitution E6, LC-21. Acceptance:
  after a run, the log holds every elaborated module and its messages. Unblocks: every later task.
- [ ] T003 Extend the timing record of `scripts/build-timing.sh` with the environment (toolchain,
  Mathlib revision from `lake-manifest.json`, host) and the input (module list), record `just loop`
  runs as well, and track `build-timings/` in Git by removing `/build-timings/` from `.gitignore`;
  update `docs/build-timings.md`. Constitution E7. Acceptance: one committed record per run with
  run, revision, environment and input. Unblocks: timing triage (E8).

## Phase 2: #193, one multiplication and one addition (US1, unblocks kernel T131 and T055)

- [ ] T004 [US1] #193: run and record in the issue the search of plan.md "Search before
  authoring" (row #193). Acceptance: the record names each query, each surface and each hit.
- [ ] T005 [US1] #193: declare `op.magmas.mul` and `op.additive_magmas.add`; make every row of
  monoids, semigroups, groups, semirings, rings and modules a `refines` restriction with its
  agreement theorem; register the structural chain additive monoids → additive semigroups →
  additive magmas → sets and semirings → additive commutative monoids; set
  `fun.additive_groups.to_groups` non-structural; add the negation row at `cat.additive_groups`,
  refined by `op.rings.neg`; add `cell.rings.additive_monoid.routes` (`data-model.md` cells); give
  `cat.magmaswithtwooperations` its two magmas as structural functors. Files:
  `Sem/Algebra/Catalogue/Magmas.lean`, `Sem/Algebra/CatalogueRegistration.lean`,
  `Sem/Algebra/MonoidOperations.lean`, `Sem/Algebra/AdditiveOperations.lean`,
  `Sem/Algebra/Semirings.lean`, `Sem/Algebra/NamedRings.lean`,
  `Sem/Algebra/MonoidOperationAgreement.lean`, `Sem/Algebra/Ports.lean`,
  `Sem/Algebra/ComputationDerivations.lean`. Decision: research D1. Acceptance in
  `Reg/OperationBindingTests.lean`: on $\mathbb{Z}$, `·` resolves to `op.magmas.mul` at
  $U_\times(\mathbb{Z})$ through the restriction chain; no route gives `·` to an additive group;
  `cat.additive_magmas` and `cat.additive_semigroups` reach `cat.sets`. Unblocks: kernel T055.

## Phase 3: #200, the cycle through subsets (US1, unblocks kernel T138 and T056)

- [ ] T006 [US1] #200: record the search (plan.md row #200) in the issue.
- [ ] T007 [US1] #200: add the invertible cell `cell.sets.whole_subset.domain` with identity
  components, the theorem that $\mathrm{whole} \circ \mathrm{dom}$ is not isomorphic to the identity
  (witness $\emptyset \subseteq \{0\}$), and the validator rule that each structural cycle carries a
  cell to the identity. Files: `Sem/Foundation/Subsets.lean`, `Reg/Semantic.lean`. Decision:
  research D2. Acceptance in `Reg/RouteSearchCompleteness.lean`: every route from a set to `Sets`
  through `Subobjects(Sets)` is identified with the identity by the one cell; a test cycle with no
  cell is refused. Unblocks: kernel T056.

## Phase 4: #185, computation reference of an application (US2, unblocks kernel T121 and T032)

- [ ] T008 [US2] #185: record the search (plan.md row #185) in the issue.
- [ ] T009 [US2] #185: add `ComputationRef.application (object : ObjectId)` resolving to
  `ObjectEntry.application`, and its validation in derivations. Files: `Reg/Computation.lean`,
  `Reg/Semantic.lean`. Decision: research D3; `data-model.md` `ComputationRef.application`. Acceptance in
  `Reg/ComputationProbes.lean`: a derivation with target `obj.sets.polynomials#application` and one
  with it as prerequisite validate; a reference to an object with no application is refused.
  Unblocks: kernel T032.

## Phase 5: #183, proof procedures of literal obligations (US2, unblocks kernel T119 and T113)

- [ ] T010 [US2] #183: record the search (plan.md row #183) in the issue.
- [ ] T011 [US2] #183: add `NumeralEntry.evidence`, `GraphLiteralEntry.evidence`,
  `LiteralEntry.closing` and their procedures; `num.sets.fin` names the procedure for $k < n$;
  ring numerals name none (`data-model.md` `NumeralEntry.evidence`, `GraphLiteralEntry.evidence`,
  `LiteralEntry.closing`). Files: `Reg/Entry.lean`, `Reg/Semantic.lean`,
  `Sem/Foundation/Morphisms.lean`, `Sem/Foundation/Cardinality.lean`, `Sem/Foundation/FiniteObjects.lean`
  (the graph-literal and literal rows). Decision: research D4.
  Acceptance in `Sem/EvidenceTests.lean`: the numeral $7$ of $\mathbb{Z}/7$ is accepted and equals
  $0$; the position $7$ of `Fin 7` is refuted; `7 < 12` is proved; a graph literal on `Fin 3` is
  settled both ways; a statement with a free variable stays unsettled. Unblocks: kernel T113, T034,
  T035.

## Phase 6: #191, power-object maps (US2, unblocks kernel T129 and T113)

- [ ] T012 [US2] #191: record the search (plan.md row #191) in the issue.
- [ ] T013 [US2] #191: add morphism rows `mor.sets.member`, `mor.sets.extent`, `mor.sets.image`,
  `mor.sets.inverse_image`; the transpose at every stage with its two inverse laws, the global
  transpose as its case $Y = 1$; the adjunction of direct and inverse image; the theorem relating
  membership to `fun.subsets.contains`; the fields of `PowerObjectEntry` name the rows
  (`data-model.md` `PowerObjectEntry.member`, `.extent`, `.image`, `.inverseImage`, `.transposeAt`). Files:
  `Sem/Foundation/PowerSets.lean`, `Sem/Foundation/Subsets.lean`, `Reg/Entry.lean`. Decision:
  research D5. Acceptance in `Sem/FiniteSubsetLiteralTests.lean`: a derivation names each of the
  five families; $f^{-1}(B) \supseteq A \iff f(A) \subseteq B$ is a registered theorem. Unblocks:
  kernel T113, T035.

## Phase 7: #186, the numeral of additive monoids (US1, unblocks kernel T122 and T034)

- [ ] T014 [US1] #186: record the search (plan.md row #186) in the issue.
- [ ] T015 [US1] #186: add `num.additive_monoids`, the image of the unique map from the zero
  monoid; an additive monoid has no other numeral. File: `Sem/Algebra/AdditiveOperations.lean`.
  Decision: research D6. Acceptance in `Sem/EvidenceTests.lean`: `0` in $\mathbb{Q}^n$ reads as the
  zero vector; `1` in an additive monoid has no numeral row. Unblocks: kernel T034.

## Phase 8: #194, numerals of semirings and rings (US1, unblocks kernel T132 and T034)

- [ ] T016 [US1] #194: record the search (plan.md row #194) in the issue.
- [ ] T017 [US1] #194: add `obj.additive_monoids.naturals`, the category
  `cat.additive_monoids_with_one` = `coslice(cat.additive_monoids, obj.additive_monoids.naturals)` with the structural coslice
  forget of `ctor.coslice`, the numeral row there, the functor $S \mapsto (U_+(S), 1)$, and the
  restriction theorems of `num.semirings` and `num.rings` (`Int.cast_natCast`, `Nat.cast_zero`,
  `Nat.cast_one`). Files: `Sem/Algebra/AdditiveOperations.lean`, `Sem/ConstructorRegistration.lean`,
  `Sem/Algebra/Semirings.lean`, `Sem/Algebra/NamedRings.lean`. Decision: research D6. Acceptance in
  `Sem/EvidenceTests.lean`: for every ring $R$ and $k \in \mathbb{N}$ the two numerals agree, as one
  theorem about the family; `cat.coslice_sets` reaches `cat.sets` by the coslice forget. Unblocks:
  kernel T034.

## Phase 9: #184, written forms of morphisms and methods (US3, unblocks kernel T120 and T035)

- [ ] T018 [US3] #184: record the search (plan.md row #184) in the issue.
- [ ] T019 [US3] #184: add `NotationForm` and the `notation` field, the projected index and its
  refusals (`data-model.md` `MorphismEntry.notation`, `MethodEntry.notation`, `NotationForm`);
  declare the forms of absolute value (`mor.sets.complex_abs`), square root,
  cardinality (`meth.cardinality`), image (`mor.sets.direct_image`), coefficient
  (`mor.sets.power_series_coefficient`), derivative and division (`mor.sets.divide`, infix). Files:
  `Reg/Entry.lean`, `Reg/Semantic.lean`, `Sem/Algebra/NumberSystems.lean`,
  `Sem/Algebra/Differentials.lean`, `Sem/Foundation/Cardinality.lean`, `Sem/Foundation/PowerSets.lean`,
  `Sem/Algebra/Calculus.lean`, `Sem/Algebra/Units.lean`. Decision: research D7. Acceptance in `Reg/PresentationProbes.lean`:
  `|x|` at the reals gives the absolute value; `|X|` at finite sets gives the cardinality; a second
  row with one form at one owner is refused; a notation equal to the call form of `name` is
  refused. Unblocks: kernel T035, T036, T075.

## Phase 10: #189, multivariate polynomial rings (US3, unblocks kernel T125 and T036)

- [ ] T020 [US3] #189: record the search (plan.md row #189) in the issue.
- [ ] T021 [US3] #189: add `obj.commutative_rings.mv_polynomials` for a commutative ring and an
  index type, with `refines` to `obj.rings.mv_polynomials` and the comparison to
  `obj.algebras.mv_polynomials`. File: `Sem/Algebra/Polynomials.lean`. Acceptance in
  `Sem/PolynomialContractTests.lean`: Krull dimension applies to $\mathbb{Q}[x, y]$ by its
  registered domain. Unblocks: kernel T036.

## Phase 11: #198, Spec, complements of zero, slices (US3, unblocks kernel T136 and T036)

- [ ] T022 [US3] #198: record the search (plan.md row #198) in the issue.
- [ ] T023 [US3] #198: register `ctor.opposite`; the functors Spec on
  `opposite(cat.commutative_rings)` and relative Spec; the presentations of the registered spectra;
  the construction $X \setminus \{0\}$ with inclusion and admission; the slice object from $X$ and
  $X \to Y$; the structural slice forget; the structural fibre inclusion of
  `family.schemes_over_ring`; the written forms `Spec A`, `X ∖ 0`, `X in C/Y`. Files:
  `Catalogue/Constructors.lean`, `Sem/ConstructorRegistration.lean`, `Sem/Algebra/Schemes.lean`,
  `Sem/Algebra/Polynomials.lean`. Decision: research D8. Acceptance in
  `Sem/PolynomialPresentationEvidenceTests.lean`: `obj.schemes_over.spec_polynomials` is the value
  of relative Spec at $K[x]$; `Poly∖0` is the value of the construction; `cat.schemes_over` and
  `cat.schemes_over_ring` reach `cat.schemes`. Unblocks: kernel T036, T057.

## Phase 12: #188, reading rules (US3, unblocks kernel T124 and T036)

- [ ] T024 [US3] #188: record the search (plan.md row #188) in the issue.
- [ ] T025 [US3] #188: add `ReadingEntry` (`data-model.md` `ReadingEntry.source`, `.target`,
  `.map`, `.identification`) and the rows `read.global_point`, `read.carrier`,
  `read.whole_subset`, `read.own_evaluation`. Files: `Reg/Entry.lean`, `Reg/Semantic.lean`,
  `Sem/Foundation/PowerSets.lean`, `Sem/Algebra/Polynomials.lean`. Decision: research D9.
  Acceptance in `Reg/AcceptanceProbes.lean`: $i_0$ and $i_1$ give $\{0\}$ and $\{1\}$; with no
  declared inclusion no reading applies; `p(a)` for $a \in R$ reads at $(R, \mathrm{id}_R)$ with
  `evaluation_own`. Unblocks: kernel T036, T059.

## Phase 13: #190, binder operations (US2, unblocks kernel T128 and T037)

- [ ] T026 [US2] #190: record the search (plan.md row #190) in the issue.
- [ ] T027 [US2] #190: add `ComputationRef.binder (id : BinderId)` (`data-model.md`
  `ComputationRef.binder`); register the derivations
  `sumOver_eq_sum`, `prodOver_eq_prod`, `realSeriesSum_eq`, `complexSeriesSum_eq`,
  `powerSeriesSum_eq`, `limit_eq`, and the uniqueness of the limit in a Hausdorff space. Files:
  `Reg/Computation.lean`, `Sem/Algebra/FiniteSums.lean`, `Sem/Algebra/Calculus.lean`,
  `Sem/Algebra/Series.lean`, `Sem/Algebra/RealLimits.lean`. Decision: research D3. Acceptance in
  `Reg/BinderProbes.lean`: each of the eight binders is a named family; the six identities
  validate as derivations. Unblocks: kernel T037.

## Phase 14: #192, change of values at module morphisms (US4, unblocks kernel T130 and T046)

- [ ] T028 [US4] #192: record the search (plan.md row #192) in the issue.
- [ ] T029 [US4] #192: change the parameter of `fun.bilin_module.change_value`,
  `lift.bilin_module.change_value_restriction`, `fun.quad_module.change_value` and
  `fun.lattice.change_value` to a morphism of `ModuleCat R`; declare the functors
  $\mathbf{Mod}_R \to \mathbf{Cat}$ with `changeValue_id`, `changeValue_comp`. Files:
  `Sem/Modules/Bilinear/Valued/CatalogueRegistration.lean`, `Sem/Modules/Bilinear/Valued/ChangeValueLifts.lean`,
  `Sem/Modules/Quadratic/Valued/CatalogueRegistration.lean`, `Sem/Lattices/Valued/CatalogueRegistration.lean`.
  Decision: research D10. Acceptance in a new `Sem/Modules/Bilinear/Valued/ChangeValueTests.lean`:
  a linear map admitted by `admitLinear` is accepted by all four rows. Unblocks: kernel T046.

## Phase 15: #187, names of shape objects (US3, unblocks kernel T123 and T048)

- [ ] T030 [US3] #187: record the search (plan.md row #187) in the issue.
- [ ] T031 [US3] #187: add `LimitEntry.objectNames` (`data-model.md` `LimitEntry.objectNames`) and fill it on every limit and colimit row with
  a finite shape. Files: `Reg/Entry.lean`, `Reg/Semantic.lean`, the limit rows. Decision: research
  D11. Acceptance in a new `Reg/LimitShapeNameTests.lean`: the leg at `one` of a pullback is the leg
  at `WalkingCospan.one`; a name outside the shape is refused. Unblocks: kernel T048.

## Phase 16: #197, refinement along a classifier (US4, unblocks kernel T135 and T057)

- [ ] T032 [US4] #197: record the search (plan.md row #197) in the issue.
- [ ] T033 [US4] #197: add `refineAlong` with its comparison and uniqueness for property
  classifiers, the validator refusal for structure classifiers, `PropertyEntry.evidence`
  (`data-model.md` `PropertyEntry.evidence`), and the
  procedures of the five property rows. Files: `Catalogue/Holds.lean`, `Reg/Entry.lean`,
  `Reg/Semantic.lean`, the property rows. Decision: research D12. Acceptance in
  `Reg/PropertySubcategoryAtomTests.lean`: a ring with a proof of commutativity refines to a
  commutative ring with $p(\tilde{X}) = X$; two refinements of one object coexist with their
  comparison; a refinement row for a structure classifier is refused; `is_finite` is proved for a
  finite literal set and refuted for $\mathbb{N}$. Unblocks: kernel T057.

## Phase 17: #196, universal data of the constructors (US4, unblocks kernel T134 and T061)

- [ ] T034 [US4] #196: record the search (plan.md row #196) in the issue.
- [ ] T035 [US4] #196: add `ConstructorRole` and `ConstructorEntry.role` (`data-model.md`
  `ConstructorEntry.role`); declare the data of
  each constructor, with the structural core inclusion and its naturality cell; replace the name
  test of `Reg/Semantic.lean` (core row) by the role. Files: `Reg/Entry.lean`, `Reg/Semantic.lean`,
  `Sem/ConstructorRegistration.lean`. Decision: research D13. Acceptance in
  `Reg/ComparisonProbes.lean`: the validator finds the core row by its role; the seven `cat.core_*`
  categories reach their base; the two routes $\operatorname{Core}(\mathbf{Grp}) \to \mathbf{Mon}$
  agree by the cell. Unblocks: kernel T061.

## Phase 18: #182, choice-producing operations (US2, unblocks kernel T118 and T115)

- [ ] T036 [US2] #182: record the search (plan.md row #182) in the issue.
- [ ] T037 [US2] #182: add `ResultKind` and `ChoiceFibre` (`data-model.md` `OperationEntry.result`,
  `ChoiceFibre.family`, `.admissible`, `.continuation`); declare the fibres of generators,
  bases and free covers; mark `fun.modules.rank` `fixed`; make the fibre inclusions of
  `fam.based_module`, `fam.free_cover` and `fam.coord_indexed` structural. Files: `Reg/Entry.lean`,
  `Reg/Semantic.lean`, `Catalogue/Lift.lean`, `Modules/TruncatedResolutions.lean`,
  `Modules/Bilinear/Valued/Based.lean`, `Sem/Modules/Rank.lean`. Decision: research D14.
  Acceptance in a new `Reg/ChoiceFibreTests.lean`: two distinct bases of $\mathbb{Q}^2$ are both
  admissible points; a later construction has the dependent type over the fibre; `#print axioms`
  of the rank shows `Classical.choice` and the row is `fixed`. Unblocks: kernel T115.

## Phase 19: #199, progressions and subtraction (US1, unblocks kernel T137 and T068)

- [ ] T038 [US1] #199: record the search (plan.md row #199) in the issue.
- [ ] T039 [US1] #199: add the progression, its sections and enumeration, the ellipsis
  proposition with its procedure, `op.additive_groups.sub` (refined by the ring row), and the
  subtraction of $\mathbb{N}$ on $b \le a$ with its admission. File:
  `Sem/Algebra/AdditiveOperations.lean`. Decision: research D15. Acceptance in
  `Sem/FiniteSubsetLiteralTests.lean`: `{1, 3, …}` denotes $\{1 + 2k\}$ with enumeration
  $k \mapsto 1 + 2k$; `{1, 2, 4, …}` is refuted; `2 - 5` in $\mathbb{N}$ is outside the domain.
  Unblocks: kernel T068.

## Phase 20: #195, one category for each kind of order (US5, unblocks kernel T133 and T104)

- [ ] T040 [US5] #195: record the search (plan.md row #195) in the issue, including the search
  for unbounded semilattice categories.
- [ ] T041 [US5] #195: add the categories, functors, cells and operations of plan.md FR-019;
  delete `cat.partially_ordered_sets`, `cat.totally_ordered_sets`, their functors and the second
  definition of $\mathbf{LinOrd} \to \mathbf{PartOrd}$; host the well-order classifier on
  `cat.linear_orders`; make the functors of `cat.enumerated_monotone_sets` structural with their
  cell. Files: `Sem/Foundation/PowerSets.lean`, `Sem/Foundation/CatalogueRegistration.lean`,
  `Foundation/Sets.lean`, `Foundation/WellOrderedSets.lean`,
  `Sem/Foundation/WellOrderedSetsRegistration.lean`, `ForMathlib/Order/Category/`. Decision:
  research D16. Acceptance in a new `Sem/Foundation/OrderTowerTests.lean`: `0 ≤ 1 in FinOrder(5)`
  reads the relation of preorders; $(\mathbb{Z}, \max)$ is a join-semilattice; every pair of
  parallel routes has its cell; `cat.well_ordered_sets` and `cat.enumerated_monotone_sets` reach
  `cat.sets`. Unblocks: kernel T104.

## Phase 21: Milestone

- [ ] T042 Run `just test` on `main` with all tasks above landed; record its log and timing (T002,
  T003). Acceptance: the gate is green for every file of this feature, and the axiom audit shows
  no new site. Unblocks: the kernel pin of a lean-categories revision that holds the 19 inputs.

## Dependencies & Execution Order

- Phase 1 comes first: it gives the tier-1 loop that every later task uses.
- Each issue phase depends on Phase 1 only, except: T017 uses `ctor.coslice` rows that T035 later
  gives a role; T035 gives roles to `ctor.opposite` (T023) and the slice and coslice forgets (T017,
  T023); T039 uses the additive owners of T005.
- The phase order is the order of the kernel consumers; it is not a dependency order between
  issues.

## Implementation Strategy

Deliver in phase order. Each issue closes when its acceptance holds on `main`; the kernel then
pins the revision. The milestone T042 runs once after the last phase.

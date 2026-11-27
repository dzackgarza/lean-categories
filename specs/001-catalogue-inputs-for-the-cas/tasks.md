# Tasks: Catalogue inputs for the computer-algebra roadmap

**Input**: [spec.md](spec.md), [plan.md](plan.md), [research.md](research.md),
[data-model.md](data-model.md), [contracts/registry-additions.md](contracts/registry-additions.md)

**Tests**: required. Each task's acceptance is assertions in the named test module, through the
registered declarations (constitution E2).

Paths are relative to `LeanCategories/`, except `justfile`, `scripts/` and `.gitignore` at the
repository root. `Sem/` is `Catalogue/Semantics/`. `Reg/` is `Catalogue/Registry/`.

## Format: `[ID] [P?] [Story] Description`

Each task names its issue, its files, its acceptance and the kernel task that consumes it (the
lean-cas-dsl task list, "Upstream tasks").

The check of a search task is `gh issue view <issue> --comments`: the record names each query,
each surface and each hit (constitution M8). The check of every other task is `just loop` (T001)
on its changed modules and on the test module of its acceptance; the task is done when that check
passes and its acceptance holds. Its inputs are T001, the search task of its issue and the tasks
that it names.

## Execution order

Tasks are executed in document order. The issue phases follow the document order of their
kernel upstream tasks in the kernel task list: T123, T131, T138, T121, T119, T129, T120, T128,
T124, T122, T132, T125, T136, T135, T137, T130, T118, T134, T133, T332, T328, T331, T329, T330,
T334, T335, T336, T337, T333, T338, T339, T340, T341, T227, T146, T225, T226, T228, T229, T230,
T231, T232, T233, T234; each kernel upstream task stands before its first consumer. The phases
of the COMPLAINTS.md entries (Phases 46–49, FR-047 to FR-051) follow, since no kernel task is
their upstream; the import of the two catalogue test modules (T084, FR-052) is in Phase 1
(research D29). Within an issue, the search task comes before the declaration task; the one task
of each of #212 to #225 runs its search first. Every declaration task also passes tier 1 at each change, adds its
new modules to `LeanCategories/All.lean`, and is reviewed by an author who did not write it
(constitution M10). A task closes its issue when its acceptance holds on `main`.

## Phase 1: Setup (fast feedback, logs and timing)

- [ ] T001 Add the private tier-1 recipe `loop` to `justfile`: `just loop <module> [modules]`
  builds the imports of each module (`lake build +<Module>:deps`), then elaborates the module
  source afresh with `lake env lean`, under `flock .tmp/lean.lock`, in order, and stops at the
  first error; no module is elaborated against an import that is older than its source (kernel
  `CONTRIBUTING.md`, LOOP005). Constitution E1, E4. Check: `just loop
  LeanCategories/Catalogue/Registry/OperationBindingTests.lean` finishes under 300 s on the
  research image with the shared cache; after a one-line edit of a module that the test module
  imports, the same command rebuilds that module before it elaborates the test module.
  Consumer: every later task.
- [ ] T002 Make `just loop` and `just test` write a durable log of each run to `build-logs/<commit>-<start time>.log`
  in the repository tree, through `scripts/build-timing.sh`. Constitution E6, LC-21. Acceptance:
  after a run, the log holds every elaborated module and its messages. Consumer: every later task.
- [ ] T003 Extend the timing record of `scripts/build-timing.sh` with the environment (toolchain,
  Mathlib revision from `lake-manifest.json`, host) and the input (module list), record `just loop`
  runs as well, and track `build-timings/` in Git by removing `/build-timings/` from `.gitignore`;
  update `docs/build-timings.md`. Constitution E7. Acceptance: one committed record per run with
  run, revision, environment and input. Consumer: timing triage (E8).
- [ ] T084 [US9] FR-052: import `Sem/Foundation/PowerSetsTests.lean` and
  `Sem/Foundation/FiniteOrdersTests.lean` from `Catalogue.lean` and repair what they then report.
  Files: `Catalogue.lean`, the rows the two modules cover. Decision: research D29. Check: `just
  loop Catalogue/Semantics/Foundation/PowerSetsTests.lean
  Catalogue/Semantics/Foundation/FiniteOrdersTests.lean Catalogue.lean`. Acceptance: both modules
  are in the import closure of `Catalogue.lean`, which `just test` builds; the COMPLAINTS.md entry
  "#95 — two catalogue test modules in `Foundation/` are outside the build" closes with its
  evidence. Consumer: every later task whose
  evidence these modules give.

## Phase 2: #187, names of shape objects (US3, for kernel T123 and T308)

- [ ] T030 [US3] #187: record the search (plan.md row #187) in the issue.
- [ ] T031 [US3] #187: add `LimitEntry.objectNames` (`data-model.md` `LimitEntry.objectNames`) and fill it on every limit and colimit row with
  a finite shape. Files: `Reg/Entry.lean`, `Reg/Semantic.lean`, the limit rows. Decision: research
  D11. Acceptance in a new `Reg/LimitShapeNameTests.lean`: the leg at `one` of a pullback is the leg
  at `WalkingCospan.one`; a name outside the shape is refused. Consumer: kernel T308, T048.

## Phase 3: #193, one multiplication and one addition (US1, for kernel T131 and T055)

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
  `cat.additive_magmas` and `cat.additive_semigroups` reach `cat.sets`. Consumer: kernel T055.

## Phase 4: #200, the cycle through subsets (US1, for kernel T138 and T056)

- [ ] T006 [US1] #200: record the search (plan.md row #200) in the issue.
- [ ] T007 [US1] #200: add the invertible cell `cell.sets.whole_subset.domain` with identity
  components, the theorem that $\mathrm{whole} \circ \mathrm{dom}$ is not isomorphic to the identity
  (witness $\emptyset \subseteq \{0\}$), and the validator rule that each structural cycle carries a
  cell to the identity. Files: `Sem/Foundation/Subsets.lean`, `Reg/Semantic.lean`. Decision:
  research D2. Acceptance in `Reg/RouteSearchCompleteness.lean`: every route from a set to `Sets`
  through `Subobjects(Sets)` is identified with the identity by the one cell; a test cycle with no
  cell is refused. Consumer: kernel T056.

## Phase 5: #185, computation reference of an application (US2, for kernel T121 and T032)

- [ ] T008 [US2] #185: record the search (plan.md row #185) in the issue.
- [ ] T009 [US2] #185: add `ComputationRef.application (object : ObjectId)` resolving to
  `ObjectEntry.application`, and its validation in derivations. Files: `Reg/Computation.lean`,
  `Reg/Semantic.lean`. Decision: research D3; `data-model.md` `ComputationRef.application`. Acceptance in
  `Reg/ComputationProbes.lean`: a derivation with target `obj.sets.polynomials#application` and one
  with it as prerequisite validate; a reference to an object with no application is refused.
  Consumer: kernel T032.

## Phase 6: #183, proof procedures of literal obligations (US2, for kernel T119 and T113)

- [ ] T010 [US2] #183: record the search (plan.md row #183) in the issue.
- [ ] T011 [US2] #183: replace the numeral row `num.sets.fin` by the inclusion
  $\operatorname{Fin} n \hookrightarrow \mathbb N$, the admission `finPoint` and its evidence
  procedure for $k < n$ on `obj.sets.fin` (`data-model.md` `obj.sets.fin` rows, `NumeralEntry`
  docstring); add `GraphLiteralEntry.evidence`, `LiteralEntry.closing` and their procedures; ring
  numerals name none (`data-model.md` `GraphLiteralEntry.evidence`, `LiteralEntry.closing`).
  Files: `Reg/Entry.lean`, `Reg/Semantic.lean`, `Sem/Foundation/Morphisms.lean`,
  `Sem/Foundation/Cardinality.lean`, `Sem/Foundation/FiniteObjects.lean` (the graph-literal and
  literal rows). Decisions: research D4, D24.
  Acceptance in `Sem/EvidenceTests.lean`: the numeral $7$ of $\mathbb{Z}/7$ is accepted and equals
  $0$; the admission of $7$ into `Fin 7` is refuted; `7 < 12` is proved; a graph literal on `Fin 3`
  is settled both ways; a statement with a free variable stays unsettled; no numeral row of the
  snapshot has a proposition parameter. Consumer: kernel T113, T034, T035.

## Phase 7: #191, power-object maps (US2, for kernel T129 and T113)

- [ ] T012 [US2] #191: record the search (plan.md row #191) in the issue.
- [ ] T013 [US2] #191: add morphism rows `mor.sets.member`, `mor.sets.extent`, `mor.sets.image`,
  `mor.sets.inverse_image`; the transpose at every stage with its two inverse laws, the global
  transpose as its case $Y = 1$; the adjunction of direct and inverse image; the theorem relating
  membership to `fun.subsets.contains`; the fields of `PowerObjectEntry` name the rows
  (`data-model.md` `PowerObjectEntry.member`, `.extent`, `.image`, `.inverseImage`, `.transposeAt`). Files:
  `Sem/Foundation/PowerSets.lean`, `Sem/Foundation/Subsets.lean`, `Reg/Entry.lean`. Decision:
  research D5. Acceptance in `Sem/FiniteSubsetLiteralTests.lean`: a derivation names each of the
  five families; $f^{-1}(B) \supseteq A \iff f(A) \subseteq B$ is a registered theorem. Consumer:
  kernel T113, T035.

## Phase 8: #184, written forms of morphisms and methods (US3, for kernel T120 and T315)

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
  refused. Consumer: kernel T315, T035, T036, T075.

## Phase 9: #190, binder operations (US2, for kernel T128 and T037)

- [ ] T026 [US2] #190: record the search (plan.md row #190) in the issue.
- [ ] T027 [US2] #190: add `ComputationRef.binder (id : BinderId)` (`data-model.md`
  `ComputationRef.binder`); register the derivations
  `sumOver_eq_sum`, `prodOver_eq_prod`, `realSeriesSum_eq`, `complexSeriesSum_eq`,
  `powerSeriesSum_eq`, `limit_eq`, and the uniqueness of the limit in a Hausdorff space. Files:
  `Reg/Computation.lean`, `Sem/Algebra/FiniteSums.lean`, `Sem/Algebra/Calculus.lean`,
  `Sem/Algebra/Series.lean`, `Sem/Algebra/RealLimits.lean`. Decision: research D3. Acceptance in
  `Reg/BinderProbes.lean`: each of the eight binders is a named family; the six identities
  validate as derivations. Consumer: kernel T037.

## Phase 10: #188, reading rules (US3, for kernel T124 and T036)

- [ ] T024 [US3] #188: record the search (plan.md row #188) in the issue.
- [ ] T025 [US3] #188: add `ReadingEntry` (`data-model.md` `ReadingEntry.source`, `.target`,
  `.map`, `.identification`) and the rows `read.global_point`, `read.carrier`,
  `read.whole_subset`, `read.own_evaluation`. Files: `Reg/Entry.lean`, `Reg/Semantic.lean`,
  `Sem/Foundation/PowerSets.lean`, `Sem/Algebra/Polynomials.lean`. Decision: research D9.
  Acceptance in `Reg/AcceptanceProbes.lean`: $i_0$ and $i_1$ give $\{0\}$ and $\{1\}$; with no
  declared inclusion no reading applies; `p(a)` for $a \in R$ reads at $(R, \mathrm{id}_R)$ with
  `evaluation_own`. Consumer: kernel T036, T059.

## Phase 11: #186, the numeral of additive monoids (US1, for kernel T122 and T034)

- [ ] T014 [US1] #186: record the search (plan.md row #186) in the issue.
- [ ] T015 [US1] #186: add `num.additive_monoids`, the image of the unique map from the zero
  monoid; an additive monoid has no other numeral. File: `Sem/Algebra/AdditiveOperations.lean`.
  Decision: research D6. Acceptance in `Sem/EvidenceTests.lean`: `0` in $\mathbb{Q}^n$ reads as the
  zero vector; `1` in an additive monoid has no numeral row. Consumer: kernel T034.

## Phase 12: #194, numerals of semirings and rings (US1, for kernel T132 and T034)

- [ ] T016 [US1] #194: record the search (plan.md row #194) in the issue.
- [ ] T017 [US1] #194: add `obj.additive_monoids.naturals`, the category
  `cat.additive_monoids_with_one` = `coslice(cat.additive_monoids, obj.additive_monoids.naturals)` with the structural coslice
  forget of `ctor.coslice`, the numeral row there, the functor $S \mapsto (U_+(S), 1)$, and the
  restriction theorems of `num.semirings` and `num.rings` (`Int.cast_natCast`, `Nat.cast_zero`,
  `Nat.cast_one`). Files: `Sem/Algebra/AdditiveOperations.lean`, `Sem/ConstructorRegistration.lean`,
  `Sem/Algebra/Semirings.lean`, `Sem/Algebra/NamedRings.lean`. Decision: research D6. Acceptance in
  `Sem/EvidenceTests.lean`: for every ring $R$ and $k \in \mathbb{N}$ the two numerals agree, as one
  theorem about the family; `cat.coslice_sets` reaches `cat.sets` by the coslice forget. Consumer:
  kernel T034.

## Phase 13: #189, multivariate polynomial rings (US3, for kernel T125 and T036)

- [ ] T020 [US3] #189: record the search (plan.md row #189) in the issue.
- [ ] T021 [US3] #189: add `obj.commutative_rings.mv_polynomials` for a commutative ring and an
  index type, with `refines` to `obj.rings.mv_polynomials` and the comparison to
  `obj.algebras.mv_polynomials`. File: `Sem/Algebra/Polynomials.lean`. Acceptance in
  `Sem/PolynomialContractTests.lean`: Krull dimension applies to $\mathbb{Q}[x, y]$ by its
  registered domain. Consumer: kernel T036.

## Phase 14: #198, Spec, complements of zero, slices (US3, for kernel T136 and T036)

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
  `cat.schemes_over_ring` reach `cat.schemes`. Consumer: kernel T317, T036, T057.

## Phase 15: #197, refinement along a classifier (US4, for kernel T135 and T057)

- [ ] T032 [US4] #197: record the search (plan.md row #197) in the issue.
- [ ] T033 [US4] #197: add `refineAlong` with its comparison and uniqueness for property
  classifiers, the validator refusal for structure classifiers, `PropertyEntry.evidence`
  (`data-model.md` `PropertyEntry.evidence`), and the
  procedures of the five property rows. Files: `Catalogue/Holds.lean`, `Reg/Entry.lean`,
  `Reg/Semantic.lean`, the property rows. Decision: research D12. Acceptance in
  `Reg/PropertySubcategoryAtomTests.lean`: a ring with a proof of commutativity refines to a
  commutative ring with $p(\tilde{X}) = X$; two refinements of one object coexist with their
  comparison; a refinement row for a structure classifier is refused; `is_finite` is proved for a
  finite literal set and refuted for $\mathbb{N}$. Consumer: kernel T057.

## Phase 16: #199, progressions and subtraction (US1, for kernel T137 and T316)

- [ ] T038 [US1] #199: record the search (plan.md row #199) in the issue.
- [ ] T039 [US1] #199: add the progression, its sections and enumeration, the ellipsis
  proposition with its procedure, `op.additive_groups.sub` (refined by the ring row), and the
  subtraction of $\mathbb{N}$ on $b \le a$ with its admission. File:
  `Sem/Algebra/AdditiveOperations.lean`. Decision: research D15. Acceptance in
  `Sem/FiniteSubsetLiteralTests.lean`: `{1, 3, …}` denotes $\{1 + 2k\}$ with enumeration
  $k \mapsto 1 + 2k$; `{1, 2, 4, …}` is refuted; `2 - 5` in $\mathbb{N}$ is outside the domain.
  Consumer: kernel T316, T068.

## Phase 17: #192, change of values at module morphisms (US4, for kernel T130 and T046)

- [ ] T028 [US4] #192: record the search (plan.md row #192) in the issue.
- [ ] T029 [US4] #192: change the parameter of `fun.bilin_module.change_value`,
  `lift.bilin_module.change_value_restriction`, `fun.quad_module.change_value` and
  `fun.lattice.change_value` to a morphism of `ModuleCat R`; declare the functors
  $\mathbf{Mod}_R \to \mathbf{Cat}$ with `changeValue_id`, `changeValue_comp`. Files:
  `Sem/Modules/Bilinear/Valued/CatalogueRegistration.lean`, `Sem/Modules/Bilinear/Valued/ChangeValueLifts.lean`,
  `Sem/Modules/Quadratic/Valued/CatalogueRegistration.lean`, `Sem/Lattices/Valued/CatalogueRegistration.lean`.
  Decision: research D10. Acceptance in a new `Sem/Modules/Bilinear/Valued/ChangeValueTests.lean`:
  a linear map admitted by `admitLinear` is accepted by all four rows. Consumer: kernel T046.

## Phase 18: #182, choice-producing operations (US2, for kernel T118 and T115)

- [ ] T036 [US2] #182: record the search (plan.md row #182) in the issue.
- [ ] T037 [US2] #182: add `ResultKind` and `ChoiceFibre` (`data-model.md` `OperationEntry.result`,
  `ChoiceFibre.family`, `.admissible`, `.continuation`); declare the fibres of generators,
  bases and free covers; mark `fun.modules.rank` `fixed`; make the fibre inclusions of
  `fam.based_module`, `fam.free_cover` and `fam.coord_indexed` structural. Files: `Reg/Entry.lean`,
  `Reg/Semantic.lean`, `Catalogue/Lift.lean`, `Modules/TruncatedResolutions.lean`,
  `Modules/Bilinear/Valued/Based.lean`, `Sem/Modules/Rank.lean`. Decision: research D14.
  Acceptance in a new `Reg/ChoiceFibreTests.lean`: two distinct bases of $\mathbb{Q}^2$ are both
  admissible points; a later construction has the dependent type over the fibre; `#print axioms`
  of the rank shows `Classical.choice` and the row is `fixed`. Consumer: kernel T115.

## Phase 19: #196, universal data of the constructors (US4, for kernel T134 and T061)

- [ ] T034 [US4] #196: record the search (plan.md row #196) in the issue.
- [ ] T035 [US4] #196: add `ConstructorRole` and `ConstructorEntry.role` (`data-model.md`
  `ConstructorEntry.role`); declare the data of
  each constructor, with the structural core inclusion and its naturality cell; replace the name
  test of `Reg/Semantic.lean` (core row) by the role. Files: `Reg/Entry.lean`, `Reg/Semantic.lean`,
  `Sem/ConstructorRegistration.lean`. Decision: research D13. Acceptance in
  `Reg/ComparisonProbes.lean`: the validator finds the core row by its role; the seven `cat.core_*`
  categories reach their base; the two routes $\operatorname{Core}(\mathbf{Grp}) \to \mathbf{Mon}$
  agree by the cell. Consumer: kernel T061.

## Phase 20: #195, one category for each kind of order (US5, for kernel T133 and T207)

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
  `cat.sets`. Consumer: kernel T207.

## Phase 21: #216, the power of cardinals (US8, for kernel T332 and T201)

- [ ] T065 [US8] #216 (FR-033): run and record in the issue the search of plan.md "Search before
  authoring" (row #216); then add the operation `op.cardinals.power` at `cat.cardinals`, declared
  by `Cardinal.power`, with its value $n^m$ on finite cardinals and the theorem
  $|\mathcal{P}(A)| = 2^{|A|}$. File: `Sem/Foundation/Cardinality.lean`. Acceptance in a new
  `Sem/Foundation/CardinalArithmeticTests.lean`: $|\mathcal{P}(A)| = 8$ for a set $A$ with three
  elements through the row; $2^3 = 8$ in `cat.cardinals`; the issue holds the search record.
  Consumer: kernel T201.

## Phase 22: #212, a rational approximation of a real number (US8, for kernel T328 and T202)

- [ ] T066 [US8] #212 (FR-034): run and record the search (plan.md row #212); then add the
  `choice` operation `mor.sets.real_approximation` on $\mathbb{R} \times \mathbb{Q}_{>0}$ with its
  `ChoiceFibre` (fibre $\{a \in \mathbb{Q} \mid |x - a| < \varepsilon\}$, admissibility,
  inhabitation by `exists_rat_btwn`) and a result that retains $x$, $\varepsilon$ and $a$. File:
  `Sem/Algebra/NumberSystems.lean`. Decision: FR-017 (#182). Acceptance in a new
  `Sem/Algebra/NumberSystemsTests.lean`: two distinct rationals within $1/1000$ of $\sqrt{2}$ are
  both admissible points; $1$ is not admissible for $\sqrt{2}$ at $\varepsilon = 1/10$; the issue
  holds the search record. Consumer: kernel T202.

## Phase 23: #215, the square root on ℂ (US8, for kernel T331 and T202)

- [ ] T067 [US8] #215 (FR-035): run and record the search (plan.md row #215); then add the `fixed`
  morphism `mor.sets.complex_sqrt` $\mathbb{C} \to \mathbb{C}$, $z \mapsto z^{1/2}$ by
  `Complex.cpow`, with its notation `√` (FR-008). File: `Sem/Algebra/NumberSystems.lean`.
  Decision: research D21. Acceptance in `Sem/Algebra/NumberSystemsTests.lean`:
  $\sqrt{-4} = 2i$ is a theorem through the row; $\sqrt{z}^2 = z$ for every $z$; the issue holds
  the search record. Consumer: kernel T202.

## Phase 24: #213, the factorization in a unique factorization domain (US8, for kernel T329 and T221)

- [ ] T068 [US8] #213 (FR-036): run and record the search (plan.md row #213); then add the
  morphism `mor.sets.ufd_factorization`: for a unique factorization domain with a normalization
  and $a \neq 0$, the unit $u$ and the multiset `normalizedFactors a` with $a = u \cdot \prod$.
  File: `Sem/Algebra/NamedCommutativeRings.lean`. Inputs: 009 T001 (the category of unique
  factorization domains with a normalization), done at once when it is not on `main`
  (constitution M9). Decision: research D22. Acceptance in a new
  `Sem/Algebra/FactorizationTests.lean`: at $\mathbb{Z}$, $-12$ gives the unit $-1$ and the
  factors $\{2, 2, 3\}$; the product theorem holds for the family; the issue holds the search
  record. Consumer: kernel T221.

## Phase 25: #214, primality in a commutative ring (US8, for kernel T330 and T221)

- [ ] T069 [US8] #214 (FR-037): run and record the search (plan.md row #214); then add the
  predicate `mor.sets.is_prime` $R \to \Omega$ declared by `Prime`, and its procedure at
  $\mathbb{Z}$ through `Int.prime_iff_natAbs_prime` and `mor.sets.nat_is_prime`. File:
  `Sem/Algebra/NamedCommutativeRings.lean`. Acceptance in `Sem/EvidenceTests.lean`: the procedure
  proves that $-7$ is prime and refutes it for $0$ and $1$; the issue holds the search record.
  Consumer: kernel T221.

## Phase 26: #218, the roots of a polynomial with multiplicity (US8, for kernel T334 and T221)

- [ ] T070 [US8] #218 (FR-038): run and record the search (plan.md row #218); then add the morphism
  `mor.sets.polynomial_root_multiset` $R[x] \setminus \{0\} \to \operatorname{Multiset} R$ over a
  commutative domain, declared by `Polynomial.roots`, with the count theorem and the theorem that
  its underlying set is the value of `mor.sets.polynomial_roots`. File:
  `Sem/Algebra/Polynomials.lean`. Acceptance in `Sem/PolynomialContractTests.lean`:
  $(x - 1)^2 (x + 2)$ has the root multiset $\{1, 1, -2\}$ and the root set $\{1, -2\}$; the issue
  holds the search record. Consumer: kernel T221.

## Phase 27: #219, the truncation of a power series (US8, for kernel T335 and T221)

- [ ] T071 [US8] #219 (FR-039): run and record the search (plan.md row #219); then add the morphism
  `mor.sets.power_series_truncation` $R[[t]] \to R[[t]]/(t^n)$ declared by the $R$-algebra map
  `Ideal.Quotient.mkₐ R (Ideal.span {X ^ n})`, the identification of its target with
  `PowerSeries.trunc n`, and the written form $\sum_{k<n} a_k t^k + O(t^n)$. File:
  `Sem/Algebra/Series.lean`. Acceptance in a new `Sem/Algebra/SeriesTests.lean`: the truncation at
  $n = 3$ of $\sum_k (k + 1) t^k$ is $1 + 2t + 3t^2 + O(t^3)$; two series with equal coefficients
  below $n$ have equal truncations; the issue holds the search record. Consumer: kernel T221.

## Phase 28: #220, the inclusion of power series rings (US8, for kernel T336 and T221)

- [ ] T072 [US8] #220 (FR-040): run and record the search (plan.md row #220); then add the
  inclusion row `incl.sets.power_series_map` declared by `PowerSeries.map f` for an injective ring
  map $f$, with its injectivity, at `algebraMap ℚ ℝ`. File: `Sem/Algebra/Series.lean`. Acceptance
  in `Sem/Algebra/SeriesTests.lean`: $\mathbb{Q}[[t]] \subseteq \mathbb{R}[[t]]$ is a registered
  inclusion and keeps each coefficient; the issue holds the search record. Consumer: kernel T221.

## Phase 29: #221, invertibility of a matrix (US8, for kernel T337 and T221)

- [ ] T073 [US8] #221 (FR-041): run and record the search (plan.md row #221); then add the
  predicate `mor.sets.matrix_is_unit` $\mathrm{Mat}_n(R) \to \Omega$ declared by `IsUnit`, with
  `Matrix.isUnit_iff_isUnit_det` and the procedure that computes $\det M$ of a closed matrix over
  $\mathbb{Q}$. File: `Sem/Algebra/LinearAlgebra.lean`. Acceptance in `Sem/EvidenceTests.lean`:
  the procedure proves that $\begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix}$ is a unit of
  $\mathrm{Mat}_2(\mathbb{Q})$ and refutes it for $\begin{pmatrix} 1 & 2 \\ 2 & 4 \end{pmatrix}$;
  the issue holds the search record. Consumer: kernel T221.

## Phase 30: #217, a linear map given by a formula (US8, for kernel T333 and T224)

- [ ] T074 [US8] #217 (FR-042): run and record the search (plan.md row #217); then add the morphism
  row `mor.modules.formula_linear_map` from a function $R^n \to R^m$ and a proof of
  `IsLinearMap`, the procedure that proves linearity for a formula linear in its binders, and the
  relation to the matrix rows by `LinearMap.toMatrix'`. Files: `Sem/Modules/LinearMaps.lean`,
  `Sem/Algebra/LinearAlgebra.lean`. Decision: research D23. Acceptance in
  `Sem/Modules/LinearMapsTests.lean`: $(x, y) \mapsto (x + y, x - y)$ on $\mathbb{Q}^2$ is
  admitted with its kernel $0$ through the kernel row; $(x, y) \mapsto (xy, 0)$ is not admitted;
  the issue holds the search record. Consumer: kernel T224.

## Phase 31: #222, the module ℤ/n (US8, for kernel T338 and T224)

- [ ] T075 [US8] #222 (FR-043): run and record the search (plan.md row #222); then add the object
  row `obj.modules.integers_mod` of `cat.modules_r` at $\mathbb{Z}$, `ModuleCat.of ℤ (ZMod n)`,
  with its written form `ℤ/n in Modules(ℤ)` and its underlying set. File:
  `Sem/Modules/CatalogueRegistration.lean`. Acceptance in `Sem/Modules/LinearMapsTests.lean`:
  `ℤ/4 in Modules(ℤ)` reads to the row, and $5 \cdot 1 = 1$ in it; the issue holds the search
  record. Consumer: kernel T224.

## Phase 32: #223, the derivative as a linear map (US8, for kernel T339 and T224)

- [ ] T076 [US8] #223 (FR-044): run and record the search (plan.md row #223); then add the morphism
  row `mor.modules.polynomial_derivative` $R[x] \to R[x]$ of $R$-modules, declared by
  `Polynomial.derivative`, with the theorem that its underlying map is
  `mor.sets.polynomial_derivative`. File: `Sem/Algebra/Differentials.lean`. Acceptance in
  `Sem/Modules/LinearMapsTests.lean`: over $\mathbb{Q}$ its kernel through the kernel row is the
  constants; the issue holds the search record. Consumer: kernel T224.

## Phase 33: #224, the enumeration of a denumerable set (US8, for kernel T340 and T250)

- [ ] T077 [US8] #224 (FR-045): run and record the search (plan.md row #224); then add the object
  rows `obj.enumerated_sets.naturals`, `obj.enumerated_sets.integers` and
  `obj.enumerated_sets.rationals` with `Denumerable.ofNat`, the morphism `mor.sets.enumeration_at`
  $k \mapsto X[k]$, and the progressions of FR-018 as objects with their enumeration. File:
  `Sem/Foundation/Catalogue.lean`. Acceptance in a new `Sem/Foundation/EnumeratedSetsTests.lean`:
  the first five terms of $\mathbb{Z}$ are $0, -1, 1, -2, 2$; the progression $\{1, 3, \ldots\}$
  has the term $5$ at $k = 2$; the issue holds the search record. Consumer: kernel T250.

## Phase 34: #225, principal ideals as objects (US8, for kernel T341 and T252)

- [ ] T078 [US8] #225 (FR-046): run and record the search (plan.md row #225); then add the object
  row `obj.ideals.principal` of `cat.ideals_r`, declared by `Ideal.span {a}`, with its written form
  `(a)`, and the theorem $\operatorname{Ann}_{\mathbb{Z}}(\mathbb{Z}/4) = (4)$ for
  `fun.modules.annihilator`. File: `Sem/Modules/Operations.lean`. Acceptance in a new
  `Sem/Modules/IdealTests.lean`: `(4)` reads to the principal ideal of $\mathbb{Z}$; the
  annihilator theorem holds; the issue holds the search record. Consumer: kernel T252.

## Phase 35: #203, an ideal as a submodule of the regular module (US7, for kernel T227 and T252)

- [ ] T047 [US7] #203: run and record in the issue the search of plan.md "Search before
  authoring" (row #203). Acceptance: the record names each query, each surface and each hit.
- [ ] T048 [US7] #203 (FR-024): add the structural functor from `cat.ideals_r` to `cat.subobjects_modules_r`, $I \mapsto (I \hookrightarrow R)$, from `Ideal R = Submodule R R`. Files: `Sem/Modules/Operations.lean`. Acceptance in a new `Reg/ScaffoldingReachTests.lean`: `cat.ideals_r` reaches `cat.sets`; the image of an ideal is a subobject of the regular module. Consumer: kernel T252.

## Phase 36: #211, ring operations and the scalar action at every universe (US1, for kernel T146 and T143)

- [ ] T063 [US1] #211: run and record in the issue the search of plan.md "Search before
  authoring" (row #211). Acceptance: the record names each query, each surface and each hit.
- [ ] T064 [US1] #211 (FR-032): declare `NamedRings.add`, `mul`, `neg`, `pow` for `R : Rings.{u}`
  and `Operations.scalarAction` for `R : RingCat.{u}`, `M : ModuleCat.{v} R`, with the rows at that
  generality. Files: `Sem/Algebra/NamedRings.lean`, `Sem/Modules/Operations.lean`. Acceptance in
  `Reg/OperationBindingTests.lean`: `·` on a ring of universe 1 resolves to the ring row, and the
  scalar action of a module of another universe than its ring is the registered one. Consumer:
  kernel T143.

## Phase 37: #201, crystals as a registered category with its underlying set (US7, for kernel T225 and the V3 task of `cat.crystals`)

- [ ] T043 [US7] #201: run and record in the issue the search of plan.md "Search before
  authoring" (row #201). Acceptance: the record names each query, each surface and each hit.
- [ ] T044 [US7] #201 (FR-022): replace the opaque expression of `cat.crystals` by a registered category; add the structural functor row to `cat.sets` declared by `crystalsToSets` (`Exceptional/Mathlib.lean:153`); delete `oport.crystals.sets` and its realization. Files: `Sem/Exceptional/Catalogue.lean`, `Sem/Exceptional/CatalogueRegistration.lean`. Decision: research D20. Acceptance in a new `Reg/ScaffoldingReachTests.lean`: `cat.crystals` reaches `cat.sets`; no opaque port of crystals remains. Consumer: the V3 task of `cat.crystals` (kernel T225).

## Phase 38: #202, the underlying set of a scheme (US7, for kernel T226 and the V3 task of `cat.schemes`)

- [ ] T045 [US7] #202: run and record in the issue the search of plan.md "Search before
  authoring" (row #202). Acceptance: the record names each query, each surface and each hit.
- [ ] T046 [US7] #202 (FR-023): register the category of topological spaces (`TopCat`) with its structural forget to `cat.sets`, and `Scheme.forgetToTop` as the structural row from `cat.schemes`. Files: a new `Sem/Foundation/TopologicalSpaces.lean`, `Sem/Algebra/Schemes.lean`. Decision: research D18. Acceptance in a new `Reg/ScaffoldingReachTests.lean`: `cat.schemes` reaches `cat.sets` through the category of topological spaces; `cat.schemes_over` reaches it through the slice forget of #198. Consumer: the V3 task of `cat.schemes` (kernel T226).

## Phase 39: #204, the inclusion of a refinement into its base (US7, for kernel T228 and the V3 task of the first refined category of forms over rings)

- [ ] T049 [US7] #204: run and record in the issue the search of plan.md "Search before
  authoring" (row #204). Acceptance: the record names each query, each surface and each hit.
- [ ] T050 [US7] #204 (FR-025): derive the edge $\mathrm{refine}(B, c) \to B$ in `SemanticState.structuralEdges` (`Reg/Semantic.lean:1680-1693`) and refuse a functor row equal to it in the immediate-functor validation. Files: `Reg/Semantic.lean`. Decision: research D17. Acceptance in a new `Reg/ScaffoldingReachTests.lean`: each of the seven refinement categories has the derived edge to its base; a row that restates one is refused. Consumer: the V3 task of the first refined category of forms over rings (kernel T228).

## Phase 40: #205, the underlying module of a bilinear form (US7, for kernel T229 and the V3 task of `cat.bilin_forms_over_rings`)

- [ ] T051 [US7] #205: run and record in the issue the search of plan.md "Search before
  authoring" (row #205). Acceptance: the record names each query, each surface and each hit.
- [ ] T052 [US7] #205 (FR-026): add the structural functor $(R, M, W, b) \mapsto (R, M)$ from `cat.bilin_forms_over_rings` to `cat.modules_over_rings_ext`. Files: `Sem/FibrationRegistration.lean`. Acceptance in a new `Reg/ScaffoldingReachTests.lean`: the new row is structural and differs from `fun.bilin_forms.values`. Consumer: the V3 task of `cat.bilin_forms_over_rings` (kernel T229).

## Phase 41: #206, the underlying module of a quadratic form (US7, for kernel T230 and the V3 task of `cat.quad_forms_over_rings`)

- [ ] T053 [US7] #206: run and record in the issue the search of plan.md "Search before
  authoring" (row #206). Acceptance: the record names each query, each surface and each hit.
- [ ] T054 [US7] #206 (FR-027): add the structural functor from `cat.quad_forms_over_rings` to `cat.modules_over_rings_ext`. Files: `Sem/QuadFibrationRegistration.lean`. Acceptance in a new `Reg/ScaffoldingReachTests.lean`: the new row is structural and differs from `fun.quad_forms.ring`. Consumer: the V3 task of `cat.quad_forms_over_rings` (kernel T230).

## Phase 42: #207, modules over commutative rings as modules over rings (US7, for kernel T231 and the V3 task of `cat.modules_over_rings_ext`)

- [ ] T055 [US7] #207: run and record in the issue the search of plan.md "Search before
  authoring" (row #207). Acceptance: the record names each query, each surface and each hit.
- [ ] T056 [US7] #207 (FR-028): add the structural functor from `cat.modules_over_rings_ext` to `cat.modules_total` over $\mathbf{CRing} \to \mathbf{Ring}$, acting on maps through `ModuleCat.extendRestrictScalarsAdj`, with the theorem that it commutes with `fun.modules_ext.ring` and `fun.modules.projection`. Files: `Sem/FibrationRegistration.lean`. Decision: research D19. Acceptance in a new `Reg/ScaffoldingReachTests.lean`: `cat.modules_over_rings_ext`, `cat.bilin_forms_over_rings` and `cat.quad_forms_over_rings` reach `cat.sets`; the commuting theorem holds. Consumer: the V3 task of `cat.modules_over_rings_ext` (kernel T231).

## Phase 43: #208, the lattice of a cusp (US7, for kernel T232 and the V3 task of `cat.cusps`)

- [ ] T057 [US7] #208: run and record in the issue the search of plan.md "Search before
  authoring" (row #208). Acceptance: the record names each query, each surface and each hit.
- [ ] T058 [US7] #208 (FR-029): add the structural functor from `cat.cusps` to `cat.integral_lattice`, declared by `CuspObject.lattice` and the embedding of a cusp morphism. Files: `Lattices/Valued/Cusps.lean`. Decision: research D20. Acceptance in a new `Reg/ScaffoldingReachTests.lean`: `cat.cusps` reaches `cat.sets`; the image of $(L, \Gamma)$ is $L$. Consumer: the V3 task of `cat.cusps` (kernel T232).

## Phase 44: #209, definite and indefinite lattices as finite projective lattices (US7, for kernel T233 and the V3 tasks of `cat.definite_lattice` and `cat.indefinite_lattice`)

- [ ] T059 [US7] #209: run and record in the issue the search of plan.md "Search before
  authoring" (row #209). Acceptance: the record names each query, each surface and each hit.
- [ ] T060 [US7] #209 (FR-030): register `definiteForget` and `indefiniteForget` (`Lattices/Valued/DefiniteIndefinite.lean:46`, `:57`) as structural rows into `cat.finite_projective_lattice` at $(\mathbb{Z}, \mathbb{Z})$. Files: `Sem/Lattices/Valued/CatalogueRegistration.lean`. Decision: research D20. Acceptance in a new `Reg/ScaffoldingReachTests.lean`: both categories reach `cat.sets`. Consumer: the V3 tasks of `cat.definite_lattice` and `cat.indefinite_lattice` (kernel T233).

## Phase 45: #210, the inclusions of the finite free, even and unimodular lattice families (US7, for kernel T234 and the V3 tasks of the finite free, even and unimodular lattice families)

- [ ] T061 [US7] #210: run and record in the issue the search of plan.md "Search before
  authoring" (row #210). Acceptance: the record names each query, each surface and each hit.
- [ ] T062 [US7] #210 (FR-031): register the three full-subcategory inclusions (`Lattices/Valued/Arithmetic.lean:40-46`, `ScaleAndEvenness.lean:265`, `MetricDual.lean:166`) as structural rows at the parameters of each family. Files: `Sem/Lattices/Valued/CatalogueRegistration.lean`. Decision: research D20. Acceptance in a new `Reg/ScaffoldingReachTests.lean`: `cat.finite_free_lattice`, `cat.even_lattice` and `cat.unimodular_lattice` reach `cat.sets`. Consumer: the V3 tasks of the finite free, even and unimodular lattice families (kernel T234).

## Phase 46: Catalogue rows in their categorical form (US9, FR-047, FR-048)

- [ ] T079 [US9] FR-047, FR-048: find every catalogue declaration that takes a bare carrier with an
  instance argument (a binder `(X : Type …) [inst]`) and move it onto an object of the category
  that carries the structure, with its units and operations along the structural routes; confirm
  at the task revision that each row of the COMPLAINTS.md entry "Catalogue rows in violation of
  LC-13, LC-14 and LC-15" is total out of its domain object and repair any that is not. Files:
  plan.md "Catalogue defects recorded in COMPLAINTS.md", rows FR-047 and FR-048. Acceptance in
  `Sem/BinderTests.lean` and `Sem/TotalityProbes.lean`: no catalogue declaration has a bare-carrier
  binder; both entries close with their evidence.

## Phase 47: Membership evidence (US9, FR-049)

- [ ] T080 [US9] FR-049 (a), (b): the Pratt-certificate procedure for primes and the unit
  characterizations of research D28. Files: `Sem/Algebra/{Semirings,Units,LinearAlgebra}.lean`.
  Decision: D28. Acceptance in `Sem/EvidenceTests.lean`: $2^{31} - 1$ is proved prime at the default
  recursion depth; $1 + 2x \in (\mathbb Z/4)[x]$, $(u, v) \in M \times N$ for units $u, v$, $i \in \mathbb Z[i]$
  and the transpose of a unit matrix are units; $2x$ is refused over $\mathbb Z$.
- [ ] T081 [US9] FR-049 (c), (d), (e): certified interval bounds for real nonzero values after the
  search of constitution M8, the polynomial expressions and non-injective images of research D28,
  and the piecewise and removable continuity and smoothness cases. Files:
  `Sem/Algebra/{PolynomialEvidence,LinearAlgebra,Calculus}.lean`. Decision: D28. Acceptance in
  `Sem/EvidenceTests.lean` and `Sem/PolynomialContractTests.lean`: $\pi - 3 \neq 0$;
  $(x^2 + 5) \mapsto \mathbb Z/5$ is nonzero; $(6x^2 + x) \mapsto \mathbb Z/5$ is monic of degree
  $2$; $x \mapsto |x|$ written by cases is continuous; the COMPLAINTS.md entry "Membership evidence
  (LC-18)" closes with its evidence.

## Phase 48: The product of groups (US9, FR-050)

- [ ] T082 [US9] FR-050: register `lim.groups.product` with `standardization := diagramIsoPair` and
  `dataConstructor := BinaryFan.mk` from `groupProductFan` and `groupProductIsLimit`. Files:
  `Sem/Limits/Registration.lean`. Acceptance in `Algebra/GroupProductTests.lean`: the product of
  $\mathbb Z/2$ and $\mathbb Z/3$ through the row is $\mathbb Z/2 \times \mathbb Z/3$ with its universal
  property; the COMPLAINTS.md entry closes with its evidence.

## Phase 49: Registry gates (US9, FR-051)

- [ ] T083 [US9] FR-051 (d): the totality table of research D27 in `Reg/Totality.lean` and the
  refusal it drives; the gate's docstring states its scope. Files: `Reg/Totality.lean`. Decision:
  D27. Acceptance in `Sem/TotalityProbes.lean`: a row declaring `Polynomial.roots` on all of $R[x]$
  is refused and the registered row on $R[x] \setminus \{0\}$ is accepted.
- [ ] T085 [US9] FR-051 (b): `obj.sets.units` and `mor.sets.units_inverse` cite their
  identifications with the units functor (`data-model.md` `ObjectFunctorPresentation`). Files:
  `Reg/Entry.lean`, `Sem/Algebra/Units.lean`. Decision: D26. Acceptance in
  `Sem/UnitInverseTests.lean`: a reader finds the identification of `Units` with the underlying set
  of $(-)^\times(M)$ through the row; the COMPLAINTS.md entry closes with its evidence.
- [ ] T086 [US9] FR-051 (a): $\operatorname{Aut}$ and $\operatorname{Stab}$ as constructions generic in
  the category (`data-model.md` `ConstructionEntry` category parameter); the per-category rows
  become its applications. Files: `Reg/Entry.lean`, `Reg/Semantic.lean`,
  `Sem/Algebra/Automorphisms.lean`. Decision: D25. Acceptance in a new
  `Reg/GenericConstructionTests.lean`: $\operatorname{Aut}_{\mathbf{Grp}}(\mathbb Z/3) \cong \mathbb Z/2$ while
  $\operatorname{Aut}_{\mathbf{Set}}$ of its underlying set is $\mathbf{Sym}(3)$; no structural route
  transports the construction; the COMPLAINTS.md entry closes with its evidence.
- [ ] T087 [US9] FR-051 (e): the registration gate of LC-16: the registry refuses an operation,
  method or endofunctor row whose declaration does not take its object in the declared category,
  so that some object of that category lacks the structure that the row uses (constitution M7).
  Files: `Reg/Semantic.lean`. Acceptance in `Sem/TotalityProbes.lean`: a row of `⁻¹` at
  `cat.monoids` is refused and the row at `cat.groups` is accepted; `CONTRIBUTING.md` LC-16 names
  this gate.

## Phase 50: Milestone

- [ ] T042 Run `just test` on `main` with all tasks above landed; record its log and timing (T002,
  T003). Acceptance: the gate is green for every file of this feature, and the axiom audit shows
  no new site. Consumer: the kernel pin of a lean-categories revision that holds the 44 inputs.

## Dependencies & Execution Order

- Phase 1 comes first: it gives the tier-1 loop that every later task uses.
- Each issue phase depends on Phase 1 only, except: T017 uses `ctor.coslice` rows that T035 later
  gives a role; T035 gives roles to `ctor.opposite` (T023) and the slice and coslice forgets (T017,
  T023); T039 uses the additive owners of T005.
- T056 (#207) gives `cat.modules_over_rings_ext` its chain; the rows of T052 and T054 (#205,
  #206) reach `cat.sets` through it, and the refinements of T050 (#204) reach it through them.
- The phase order is the order of the kernel consumers; it is not a dependency order between
  issues.
- T068 needs 009 T001 (the divisibility tower). Every task of this feature writes its new
  rows in the LC-13 form; T079 moves the rows that are already on `main`.
- T084 is in Phase 1; T080–T087 follow the scaffolding phases (research D29).

## Implementation Strategy

Deliver in phase order. Each issue closes when its acceptance holds on `main`; the kernel then
pins the revision. The milestone T042 runs once after the last phase.

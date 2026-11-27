# Implementation Plan: Catalogue inputs for the computer-algebra roadmap

**Branch**: `001-catalogue-inputs-for-the-cas` (work lands on `main`) | **Date**: 2026-11-25 | **Spec**: [spec.md](spec.md)
**Input**: Feature specification from `specs/001-catalogue-inputs-for-the-cas/spec.md`

Paths are relative to `LeanCategories/`. `Sem/` is `Catalogue/Semantics/`. `Reg/` is
`Catalogue/Registry/`. Line numbers are of `main` at `443fba9`.

## Summary

The feature adds to the registry the 44 declarations that the kernel task list consumes
(issues #182 to #225). Each declaration is stated at its generating category, from its source,
and enters through `normalized_registry`. Four schema additions carry them: a computation
reference for object applications and binder operations, a result kind with choice fibres, a
structured notation field, and constructor roles. The design decisions are in
[research.md](research.md); the schema is in [data-model.md](data-model.md); the read surface
is in [contracts/registry-additions.md](contracts/registry-additions.md).

## Technical Context

**Language/Version**: Lean 4, toolchain of `lean-toolchain` (`leanprover/lean4:v4.36.0`)
**Primary Dependencies**: Mathlib (`rev = "master"` in `lakefile.toml`, locked in `lake-manifest.json`), BrauerGroup
**Storage**: Lean source files; registry rows through `normalized_registry`
**Testing**: Lean test modules with `example`, `#guard_msgs` and theorems (`Reg/*Tests.lean`, `Reg/*Probes.lean`, `Sem/*Tests.lean`); `just test`
**Target Platform**: Linux, research image `ghcr.io/dzackgarza/sage:develop` (constitution E5)
**Project Type**: Lean library (formal mathematics and its registry)
**Performance Goals**: tier-1 loop of each task under 300 s (constitution E1, E4)
**Constraints**: one Lean process under `flock .tmp/lean.lock` (E10); no `sorry`, no axiom (M3)
**Scale/Scope**: 44 issues and 7 COMPLAINTS.md entries; 100 registered categories; 675 registry rows at `443fba9`

## Constitution Check

| Article | Check for this feature | Status |
| --- | --- | --- |
| M1 | Every declaration is mathematics of this repository; no kernel input shapes it | pass: requirements come from the issues and their sources |
| M2 | Each FR cites its source; each task compares clause by clause | pass by task acceptance |
| M3 | No `sorry`, axiom or `native_decide`; `just test` at the milestone | pass by task acceptance; the `native_decide` sites of `Reg/PresentationProbes.lean` and `Reg/ComparisonProbes.lean` are removed by feature 002 T129 |
| M4 | Each operation at its generating category; rows above it are restrictions | FR-001, FR-006, FR-007, FR-018, FR-019 |
| M5 | Total operations; domain evidence; numerals as universal images | FR-004, FR-006, FR-007, FR-018 (ℕ subtraction on $b \le a$) |
| M6 | A cell for every parallel route; chosen data never from existence | FR-001, FR-002, FR-015, FR-017, FR-019 |
| M7 | One field per meaning; schema changes owned here | data-model.md: references by existing rows; notation migrates `name` |
| M8 | Search record per issue | first task of each issue |
| M9 | Consumer workstream works here from the issue and sources | tasks name no kernel file as an input |
| M10 | Independent review of each change | task acceptance includes review by an author who did not write the change |
| M11 | This task list in document order; the corpus DAG of `TODO.md` does not order it | pass |
| E1-E9 | Tier-1 loop, durable logs, timing records | Phase 1 tasks T001-T003 |

Gate result: pass. No violation is justified in Complexity Tracking.

## Checks of this repository

| Tier | Command | Source |
| --- | --- | --- |
| Tier 1 | `just loop <modules>` (T001, the first task) for each changed module and each test module of the changed mechanism | `TODO.md` "One Lean process"; constitution E1 |
| Full gate | `just test` (build, `lean-no-sorry`, vacuity audit, Mathlib lint audit, unused-variable check, axiom audit) | `justfile` |
| CI | `just test-ci` on push | `.github/workflows/ci.yml` |

Every task passes tier 1 at each change. The full gate runs at the end of each phase.

## Search before authoring

The first task of each issue runs this search and writes the record in the issue (constitution
M8); for #212 to #225 the search is the first step of the one task of the issue: `python scripts/formalization_corpus.py search '<query>'` under each formulation, Mathlib
(Loogle, `#find`, source tree), and the broader ecosystem. The table lists the Mathlib notions to
look for.

| Issue | Mathlib notions and queries |
| --- | --- |
| #193 | `MagmaCat`, `AddMagmaCat`, `Semigrp`, `AddSemigrp`, `MonCat`, `AddMonCat`, `forget₂ SemiRingCat AddCommMonCat`, `Mul`, `Add`, `npow` |
| #200 | `Subobject`, `MonoOver`, `Subobject.underlying`, `Subobject.mk`, `Subobject.underlyingIso` |
| #185 | `CartesianClosed`, `exp.ev`, `Polynomial.eval₂`, `Matrix.mulVec` |
| #183 | `ZMod.natCast_self`, `Fin.mk`, `Nat.decLt`, `Fintype.decidableForallFintype`, `DecidableEq` |
| #191 | `Set.image`, `Set.preimage`, `Set.range`, `Set.image_subset_iff`, `Set.mem_def`, `CategoryTheory.Subobject`, `Topos` (any power-object formalization) |
| #186 | `AddMonCat`, `Limits.IsInitial`, `Zero` |
| #194 | `AddMonoidWithOne`, `Nat.cast`, `Nat.castAddMonoidHom`, `Int.cast_natCast`, `Under`, `Nat.cast_zero`, `Nat.cast_one` |
| #184 | Mathlib notation classes (`abs` notation `|a|`, `HDiv`, `Finset.card` notation) |
| #189 | `MvPolynomial`, `MvPolynomial.instCommRing`, `CommRingCat.of`, `ringKrullDim`, `MvPolynomial.ringKrullDim` |
| #198 | `Opposite`, `CategoryTheory.op`, `AlgebraicGeometry.Scheme.Spec`, `Spec.map`, `Over.mk`, `Over.forget`, `nonZeroDivisors`, `Set.compl` |
| #188 | `Polynomial.eval`, `Polynomial.aeval`, `Under.mk`, `Set.range`, `Function.Injective` |
| #190 | `Finset.sum`, `Finset.prod`, `tsum`, `Summable`, `intervalIntegral`, `Filter.Tendsto`, `tendsto_nhds_unique`, `PowerSeries` |
| #192 | `ModuleCat.ofHom`, `ModuleCat.Hom.hom`, `LinearMap.compr₂`, `LinearMap.BilinForm`, `QuadraticForm.comp` |
| #187 | `WalkingPair`, `WalkingCospan`, `WalkingSpan`, `WalkingParallelPair`, `Limits.Fan.proj` |
| #197 | `ObjectProperty.FullSubcategory`, `Functor.Fiber`, `FullSubcategory.lift` |
| #196 | `Arrow`, `Arrow.leftFunc`, `Arrow.rightFunc`, `Core`, `Core.inclusion`, `Over.forget`, `Under.forget`, `CategoryOfElements.π`, `Subobject.underlying`, `evaluation`, `opOp` |
| #182 | `Basis`, `Module.Finite`, `Module.Free`, `Module.rank`, `Submodule.span`, `Function.Surjective`, `Classical.choice` |
| #199 | `nsmul`, `Set.range`, `sub_eq_add_neg`, `Nat.sub`, `tsub` |
| #195 | `Preord`, `PartOrd`, `LinOrd`, `SemilatSupCat`, `SemilatInfCat`, `Lat`, `BddLat`, `BoolAlg`, `SupHom`, `InfHom`, `LatticeHom` |
| #201 | `Crystal` (`Exceptional/Mathlib.lean`), crystal, Kashiwara operator, `forget` |
| #202 | `AlgebraicGeometry.Scheme.forgetToTop`, `TopCat`, `forget TopCat`, `TopologicalSpace` |
| #203 | `Ideal`, `Submodule`, `Submodule.subtype`, `Subobject.mk` |
| #204 | `ObjectProperty.FullSubcategory`, `ObjectProperty.ι`, `CategoryExpr.refine`, `structuralEdges` |
| #205 | `LinearMap.BilinMap`, `CategoryTheory.Grothendieck.forget` |
| #206 | `QuadraticMap`, `QuadraticModuleCat` |
| #207 | `ModuleCat.extendScalars`, `ModuleCat.restrictScalars`, `ModuleCat.extendRestrictScalarsAdj`, `CategoryTheory.Grothendieck`, `forget₂ CommRingCat RingCat` |
| #208 | `CuspObject`, `Subgroup.FiniteIndex` |
| #209 | `ObjectProperty.ι`, `QuadraticForm.PosDef`, signature |
| #210 | `ObjectProperty.ι`, `Module.Free`, `Module.Finite` |
| #211 | `RingCat`, `ModuleCat`, universe polymorphism of `NamedRings`, `Operations.scalarAction` |
| #216 | `Cardinal.power`, `HPow Cardinal Cardinal`, `Cardinal.mk_set`, `Cardinal.natCast_pow` |
| #212 | `exists_rat_btwn`, `Rat.cast`, `abs_sub_lt_iff`, approximation, `Real` decimal expansion |
| #215 | `Complex.cpow`, `Complex.log`, `Complex.arg`, square root on `ℂ`, branch cut |
| #213 | `UniqueFactorizationMonoid`, `UniqueFactorizationMonoid.normalizedFactors`, `NormalizationMonoid`, `Int.instUniqueFactorizationMonoid`, `Int.normalize` |
| #214 | `Prime`, `Int.prime_iff_natAbs_prime`, `Ideal.span_singleton_prime`, `Ideal.IsPrime`, `Nat.Prime` decidability |
| #218 | `Polynomial.roots`, `Polynomial.rootMultiplicity`, `Polynomial.count_roots`, `Polynomial.mem_roots`, `Polynomial.rootSet` |
| #219 | `PowerSeries.trunc`, `PowerSeries.X`, `Ideal.Quotient.mk`, `Ideal.Quotient.mkₐ`, `Ideal.span` |
| #220 | `PowerSeries.map`, `algebraMap ℚ ℝ`, injectivity of `PowerSeries.map` |
| #221 | `IsUnit`, `Matrix.isUnit_iff_isUnit_det`, `Matrix.GeneralLinearGroup`, `Matrix.det` |
| #217 | `LinearMap`, `IsLinearMap`, `LinearMap.pi`, `Matrix.toLin'`, `LinearMap.toMatrix'`, `LinearMap.ker`, `LinearMap.range` |
| #222 | `ZMod`, `ModuleCat.of ℤ (ZMod n)`, `AddCommGroup.toIntModule` |
| #223 | `Polynomial.derivative`, `Polynomial.derivative` as `R[X] →ₗ[R] R[X]`, `LinearMap.ker` |
| #224 | `Denumerable`, `Denumerable.ofNat`, `Encodable`, the `Denumerable ℤ` and `Denumerable ℚ` instances |
| #225 | `Ideal.span`, `Module.annihilator`, `Submodule.annihilator`, `Ideal.span_singleton` |

## Files and registry rows per requirement

Each row gives the files to add or change and the registry rows. New modules are imported in
`LeanCategories/All.lean` by the same task (constitution M9).

### FR-001 (#193): one multiplication, one addition

- `Sem/Algebra/Catalogue/Magmas.lean`, `Sem/Algebra/CatalogueRegistration.lean`: add
  `op.magmas.mul` (`·`) at `cat.magmas` and `op.additive_magmas.add` (`+`) at
  `cat.additive_magmas`.
- `Sem/Algebra/MonoidOperations.lean` (`op.monoids.mul`, `op.monoids.one`),
  `Sem/Algebra/AdditiveOperations.lean` (`op.additive_monoids.add`), `Sem/Algebra/Semirings.lean`
  (`op.semirings.mul`, `op.semirings.add`, `op.semirings.pow`), `Sem/Algebra/NamedRings.lean`
  (`op.rings.mul`, `op.rings.add`, `op.rings.neg`, `op.rings.pow`): set `refines` to the owner
  along the stated route (`Reg/Entry.lean` `OperationEntry.refines`), with the agreement theorem.
  `op.groups.inverse` stays the owner of the inverse; `op.rings.neg` refines the negation of
  additive groups, which is added at `cat.additive_groups`.
- `Sem/Algebra/MonoidOperationAgreement.lean`: the agreement theorems for whole families
  (extend `ring_mul`).
- `Sem/Algebra/Ports.lean`: add structural `fun.additive_monoids.semigroup`,
  `fun.additive_semigroups.magma`, `fun.additive_magmas.sets`; add structural
  `fun.semirings.additive_commutative_monoid`; set `fun.additive_groups.to_groups` to
  `structural := false`.
- `Sem/Algebra/ComputationDerivations.lean`: cell `cell.rings.additive_monoid.routes` for the two
  routes $\mathbf{Ring} \to \mathbf{AddMon}$.
- `Sem/Algebra/...` row of `cat.magmaswithtwooperations`: its two magmas as structural functors.
  The category is opaque today; the task replaces the opaque expression by the atom of Mathlib's
  ring-like structure with two operations (`Mul`, `Add` on one carrier) so that the functors are
  rows.
- Tests: `Reg/OperationBindingTests.lean` (one binding per symbol on each route).

### FR-002 (#200): the cycle through `Subobjects(Sets)`

- `Sem/Foundation/Subsets.lean`: cell `cell.sets.whole_subset.domain` ($\mathrm{dom} \circ
  \mathrm{whole} \cong 1$, identity components); theorem that $\mathrm{whole} \circ \mathrm{dom}$
  is not isomorphic to the identity (counterexample: $\emptyset \subseteq \{0\}$ has domain
  $\emptyset$, while the identity keeps the ambient $\{0\}$).
- `Reg/Semantic.lean`: validation that each structural cycle carries a cell to the identity.
- Tests: `Reg/RouteSearchCompleteness.lean`, `Reg/RouteDiscovery.lean`.

### FR-003 (#185): computation reference of an application

- `Reg/Computation.lean`: constructor `ComputationRef.application (object : ObjectId)`; resolution
  to `ObjectEntry.application`.
- `Reg/Semantic.lean`: validation of the new reference in derivations.
- Tests: `Reg/ComputationProbes.lean` (a derivation with target
  `obj.sets.polynomials#application`).

### FR-004 (#183): proof procedures of literal obligations

- `Reg/Entry.lean`: `GraphLiteralEntry.evidence : Name`; `LiteralEntry.closing : Name`; the
  `NumeralEntry` docstring states that numerals are images of initial maps only (research D24).
- `Sem/Foundation/Morphisms.lean`: delete the numeral row `num.sets.fin`; give `obj.sets.fin` the
  inclusion `Fin.val` into ℕ, the admission `finPoint` and the evidence `k < n` by decision on ℕ.
- Graph-literal rows: evidence of totality and distinct arguments by decision over the finite
  domain with decidable equality.
- Literal rows: closing procedure by the decidable equality of the literal type.
- `Sem/EvidenceTests.lean`: the numeral `7` of `ZMod 7` is accepted and equals `0`; the position
  `7` of `Fin 7` is refuted; `7 < 12` is proved; a graph literal on `Fin 3` is settled; an open
  statement stays unsettled.

### FR-005 (#191): power-object maps

- `Sem/Foundation/PowerSets.lean`: morphism rows `mor.sets.member`, `mor.sets.extent`,
  `mor.sets.image`, `mor.sets.inverse_image`; the transpose at every stage
  `transposeAt (Y : Sets) : (Y ⊗ X ⟶ Ω) ≃ (Y ⟶ 𝒫 X)` with both inverse laws; the present
  `transpose` becomes its case `Y = 1`; adjunction of direct and inverse image.
- `Reg/Entry.lean` `PowerObjectEntry`: fields keep the declarations; each field also names its
  morphism row (one authority: the row; the field points to it).
- `Sem/Foundation/Subsets.lean`: theorem relating `member` to `fun.subsets.contains`.
- Tests: `Reg/LiteralDomainProbes.lean`, `Sem/FiniteSubsetLiteralTests.lean`.

### FR-006 (#186): the numeral of additive monoids

- `Sem/Algebra/AdditiveOperations.lean`: row `num.additive_monoids` with declaration
  $0 : 1 \to A$, the image of the unique map from the zero monoid.
- Tests: `Sem/EvidenceTests.lean` (`0` in $\mathbb{Q}^n$ reads as the zero vector).

### FR-007 (#194): numerals of semirings and rings

- `Sem/Algebra/AdditiveOperations.lean`: object `obj.additive_monoids.naturals` ($\mathbb{N}$);
  category row `cat.additive_monoids_with_one` = `coslice(cat.additive_monoids,
  obj.additive_monoids.naturals)`; numeral row `num.additive_monoids_with_one` (image of $k$ under
  the unique map $\mathbb{N} \to A$ that sends $1$ to the chosen element).
- `Sem/ConstructorRegistration.lean`: structural coslice forget for `ctor.coslice`.
- `Sem/Algebra/Semirings.lean`: functor $S \mapsto (U_+(S), 1)$; `num.semirings` as restriction.
- `Sem/Algebra/NamedRings.lean`: `num.rings` restriction theorem for $k \in \mathbb{N}$
  (`Int.cast_natCast`); theorems for $0$ and $1$.
- Tests: `Sem/EvidenceTests.lean`.

### FR-008 (#184): written forms of morphisms and methods

- `Reg/Entry.lean`: `NotationForm` (prefix, infix, postfix, delimited with open and close
  tokens) and `notation : Option NotationForm` on `MorphismEntry` and `MethodEntry`.
- `Reg/Semantic.lean`: the projected index from written form to rows; refusal of two rows with one
  form at one owner; refusal of a notation equal to the function-call form of `name`.
- Rows: absolute value (`|x|`) and square root in `Sem/Algebra/NumberSystems.lean`; cardinality
  (`|X|`), `image`, `coefficient` and `derivative` (`Sem/Algebra/Differentials.lean`); division
  (`/`).
- Tests: `Reg/PresentationProbes.lean`.

### FR-009 (#189): multivariate polynomial rings as commutative rings

- `Sem/Algebra/Polynomials.lean`: `obj.commutative_rings.mv_polynomials` for $(R, \sigma)$ with
  `refines` to `obj.rings.mv_polynomials`, and the comparison to the base ring of
  `obj.algebras.mv_polynomials`.
- Tests: `Sem/PolynomialContractTests.lean` (Krull dimension applies to $\mathbb{Q}[x, y]$).

### FR-010 (#198): Spec, complements of zero, objects of a slice

- `Catalogue/Constructors.lean`, `Sem/ConstructorRegistration.lean`: `ctor.opposite` with
  signature `#[.category]` and its functorial action.
- `Sem/Algebra/Schemes.lean`: functor rows `fun.commutative_rings.spec` on
  `opposite(cat.commutative_rings)` to `cat.schemes`, and the relative Spec to
  `cat.schemes_over`; `functorPresentation` of `obj.schemes_over.spec_polynomials` and
  `obj.schemes_over.spec_mv_polynomials`; notation `Spec`.
- `Sem/ConstructorRegistration.lean`: structural slice forget for `ctor.slice`; object
  constructor `Over.mk` of a slice with notation `X in C/Y`.
- `family.schemes_over_ring`: structural fibre inclusion.
- `Sem/Algebra/Polynomials.lean`: construction `nonzero` of an object with zero, with inclusion
  and admission; `obj.sets.nonzero_polynomials` as its value; notation `X ∖ 0`.
- Tests: `Sem/PolynomialPresentationEvidenceTests.lean`, `Reg/PresentationProbes.lean`.

### FR-011 (#188): reading rules

- `Reg/Entry.lean`: `ReadingEntry` with `source`, `target`, `map` (a selected morphism, route or
  inclusion row) and `identification` (theorem).
- Rows: `read.global_point` (uses `pow.sets.terminal`), `read.carrier` (selected structural
  route), `read.whole_subset` (requires an `InclusionEntry`), `read.own_evaluation`
  (`evaluation_own`, `Sem/Algebra/Polynomials.lean:71-93`).
- Tests: `Reg/AcceptanceProbes.lean`: the inclusions $i_0, i_1 : 1 \to \{0, 1\}$ give $\{0\}$ and
  $\{1\}$; with no declared inclusion no reading applies.

### FR-012 (#190): binder operations

- `Reg/Computation.lean`: constructor `ComputationRef.binder (id : BinderId)` naming the
  `operation` of the binder row.
- `Sem/Algebra/FiniteSums.lean`, `Calculus.lean`, `Series.lean`, `RealLimits.lean`: derivation
  rows for `sumOver_eq_sum`, `prodOver_eq_prod`, `realSeriesSum_eq`, `complexSeriesSum_eq`,
  `powerSeriesSum_eq`, `limit_eq`; uniqueness theorem of the limit.
- Tests: `Reg/BinderProbes.lean`, `Sem/BinderTests.lean`.

### FR-013 (#192): change of values at module morphisms

- `Sem/Modules/Bilinear/Valued/CatalogueRegistration.lean`, `ChangeValueLifts.lean`,
  `Sem/Modules/Quadratic/Valued/CatalogueRegistration.lean`,
  `Sem/Lattices/Valued/CatalogueRegistration.lean`: parameter `f : W ⟶ W'` in `ModuleCat R`;
  functors $\mathbf{Mod}_R \to \mathbf{Cat}$ with `changeValue_id`, `changeValue_comp`.
- `Sem/Modules/LinearMaps.lean`: the admission `admitLinear` serves the parameter.
- Tests: a test module `Sem/Modules/Bilinear/Valued/ChangeValueTests.lean`.

### FR-014 (#187): names of the objects of a shape

- `Reg/Entry.lean`: `LimitEntry.objectNames : Array (String × Name)`.
- Limit rows of pairs, pullbacks, pushouts, equalizers and finite products: names from Mathlib.
- Tests: `Reg/IsoCommaExample.lean` or a new `Reg/LimitShapeNameTests.lean`.

### FR-015 (#197): refinement along a classifier

- `Catalogue/Holds.lean`: `refineAlong (p) (X) (h : Holds p X)`, the comparison and the
  uniqueness, for property classifiers (`ObjectProperty.FullSubcategory`).
- `Reg/Entry.lean`: `PropertyEntry.evidence : Name`.
- `Reg/Semantic.lean`: refusal of a refinement row for a structure classifier.
- Property rows `is_finite`, `is_commutative`, `is_abelian`, `is_lattice`, `is_alternating`: their
  procedures.
- Tests: `Reg/PropertySubcategoryAtomTests.lean`.

### FR-016 (#196): universal data of the constructors

- `Reg/Entry.lean`: `ConstructorRole` and `ConstructorEntry.role`.
- `Sem/ConstructorRegistration.lean`: roles and data of `ctor.arrow`, `ctor.core`, `ctor.slice`,
  `ctor.coslice`, `ctor.elements`, `ctor.subobjects`, `ctor.functor_category`, `ctor.opposite`;
  the core inclusion as a structural functor with its naturality cell.
- `Reg/Semantic.lean:2797-2815`: find the core row by role; delete the name test.
- Tests: `Reg/ComparisonProbes.lean`.

### FR-017 (#182): choice-producing operations

- `Reg/Entry.lean`: `ResultKind` (`fixed`, `choice`) on operation, functor-method and morphism
  rows; `ChoiceFibre` with fibre family, admissibility and dependent continuation type.
- `Catalogue/Lift.lean`, `Modules/TruncatedResolutions.lean`, `Modules/Bilinear/Valued/Based.lean`:
  the fibres of generators, bases and free covers; structural fibre inclusions of
  `fam.based_module`, `fam.free_cover`, `fam.coord_indexed`.
- `Sem/Modules/Rank.lean`: `fun.modules.rank` kind `fixed`; `#print axioms` in its test shows
  `Classical.choice`.
- Tests: a test module `Reg/ChoiceFibreTests.lean`.

### FR-018 (#199): progressions and subtraction

- `Sem/Algebra/AdditiveOperations.lean`: `progression a d`, its finite sections, its enumeration;
  `op.additive_groups.sub`; `op.naturals.sub` with domain $b \le a$ and its admission.
- The ellipsis proposition and its procedure.
- Tests: `Sem/FiniteSubsetLiteralTests.lean`.

### FR-019 (#195): one category for each kind of order

- `Sem/Foundation/PowerSets.lean`: keep `cat.partial_orders`, `cat.linear_orders`; add
  `cat.preorders`, `cat.join_semilattices`, `cat.meet_semilattices`, `cat.order_lattices`,
  `cat.bounded_order_lattices`; structural functors of the tower; cells for parallel routes;
  operations `≤`, `<` at preorders, `⊔`, `⊓` at the semilattices, `min`, `max`, `⊥`, `⊤`; delete
  `fun.linear_orders.to_partial_orders` when it becomes a composite.
- `ForMathlib/Order/Category/`: categories of join- and meet-semilattices without bounds
  (Mathlib `SemilatSupCat` and `SemilatInfCat` are the bounded cases), after the search.
- `Sem/Foundation/CatalogueRegistration.lean`, `Foundation/Sets.lean`: delete
  `cat.partially_ordered_sets`, `cat.totally_ordered_sets` and their functors.
- `Sem/Foundation/WellOrderedSetsRegistration.lean`, `Foundation/WellOrderedSets.lean`: host
  `cat.linear_orders`; delete the second definition of $\mathbf{LinOrd} \to \mathbf{PartOrd}$;
  `cat.enumerated_monotone_sets` functors structural with their cell.
- `cat.boolean_algebras`: structural functor to `cat.bounded_order_lattices`; its functor to sets
  is deleted when it becomes a composite.
- Tests: a test module `Sem/Foundation/OrderTowerTests.lean`.

### FR-032 (#211): ring operations and the scalar action at every universe

- `Sem/Algebra/NamedRings.lean` (`:73-97`): `add`, `mul`, `neg`, `pow` for `R : Rings.{u}`; the
  rows of `op.rings.*` at that generality.
- `Sem/Modules/Operations.lean` (`:99`): `scalarAction` for `R : RingCat.{u}`, `M : ModuleCat.{v} R`.
- Tests: `Sem/Modules/LinearMapsTests.lean` and a universe case in `Reg/OperationBindingTests.lean`.
- Consumer: lean-cas-dsl T146, before the construction classification T143.

### Rows that the spike computations need (#212 to #225)

Line numbers and the present rows are those of `main` at `fc549ba` (the evidence of each issue).
The consumer of each row is the lean-cas-dsl category task that implements it (the leaves spec of
its category holds the row); the kernel upstream task precedes that category task.

| Requirement | Issue | Files and registry rows | Test module | Kernel upstream task, consumer |
| --- | --- | --- | --- | --- |
| FR-033 | #216 | `Sem/Foundation/Cardinality.lean`: an operation `op.cardinals.power` at `cat.cardinals` declared by `Cardinal.power`; the theorem $\lvert\mathcal{P}(A)\rvert = 2^{\lvert A \rvert}$ from `Cardinal.mk_set`; the finite value from `Cardinal.natCast_pow` | a new `Sem/Foundation/CardinalArithmeticTests.lean` | T332, Cardinals V1 (T201) |
| FR-034 | #212 | `Sem/Algebra/NumberSystems.lean`: a `choice` operation `mor.sets.real_approximation` on $\mathbb{R} \times \mathbb{Q}_{>0}$ with its `ChoiceFibre` (FR-017): fibre $\{a \in \mathbb{Q} \mid \lvert x - a \rvert < \varepsilon\}$, admissibility, inhabitation from `exists_rat_btwn`; the result retains $x$, $\varepsilon$ and $a$ | a new `Sem/Algebra/NumberSystemsTests.lean` | T328, Sets V1 (T202) |
| FR-035 | #215 | `Sem/Algebra/NumberSystems.lean`: a `fixed` morphism `mor.sets.complex_sqrt` $\mathbb{C} \to \mathbb{C}$, $z \mapsto z^{1/2}$ by `Complex.cpow`, next to `mor.sets.real_sqrt`, with the theorem $\sqrt{-4} = 2i$ and the notation of FR-008 (`√`) | `Sem/Algebra/NumberSystemsTests.lean` | T331, Sets V1 (T202) |
| FR-036 | #213 | `Sem/Algebra/NamedCommutativeRings.lean`: a morphism `mor.sets.ufd_factorization` at the unique factorization domains with a normalization (unit and multiset of normalized factors, `normalizedFactors`); its value at $\mathbb{Z}$ | a new `Sem/Algebra/FactorizationTests.lean` | T329, Commutative rings V1 (T221) |
| FR-037 | #214 | `Sem/Algebra/NamedCommutativeRings.lean`: a predicate `mor.sets.is_prime` $R \to \Omega$ on the elements of a commutative ring, declared by `Prime`, with the procedure at $\mathbb{Z}$ through `Int.prime_iff_natAbs_prime` and `mor.sets.nat_is_prime` (`Sem/Algebra/Semirings.lean:199`) | `Sem/EvidenceTests.lean` | T330, Commutative rings V1 (T221) |
| FR-038 | #218 | `Sem/Algebra/Polynomials.lean`: a morphism `mor.sets.polynomial_root_multiset` next to `mor.sets.polynomial_roots` (`:354`), declared by `Polynomial.roots`, with the count and root-set theorems | `Sem/PolynomialContractTests.lean` | T334, Commutative rings V1 (T221) |
| FR-039 | #219 | `Sem/Algebra/Series.lean`: a morphism `mor.sets.power_series_truncation` $R[[t]] \to R[[t]]/(t^n)$ declared by the $R$-algebra map `Ideal.Quotient.mkₐ R (Ideal.span {X ^ n})`, the identification of the target with `PowerSeries.trunc n`, and the notation $\sum_{k<n} a_k t^k + O(t^n)$ | a new `Sem/Algebra/SeriesTests.lean` | T335, Commutative rings V1 (T221) |
| FR-040 | #220 | `Sem/Algebra/Series.lean`: an inclusion row `incl.sets.power_series_map` declared by `PowerSeries.map f` for injective $f$, at `algebraMap ℚ ℝ` | `Sem/Algebra/SeriesTests.lean` | T336, Commutative rings V1 (T221) |
| FR-041 | #221 | `Sem/Algebra/LinearAlgebra.lean`: a predicate `mor.sets.matrix_is_unit` $\mathrm{Mat}_n(R) \to \Omega$ declared by `IsUnit`, with `Matrix.isUnit_iff_isUnit_det` and the procedure that computes $\det M$ of a closed matrix over $\mathbb{Q}$ | `Sem/EvidenceTests.lean` | T337, Commutative rings V1 (T221) |
| FR-042 | #217 | `Sem/Modules/LinearMaps.lean`, `Sem/Algebra/LinearAlgebra.lean`: a morphism row `mor.modules.formula_linear_map` from a function $R^n \to R^m$ and a proof of `IsLinearMap`, with the procedure that settles linearity for a formula linear in its binders; kernel and image through `mor.sets.matrix_ker` and the image row by `LinearMap.toMatrix'` | `Sem/Modules/LinearMapsTests.lean` | T333, Modules V1 (T224) |
| FR-043 | #222 | `Sem/Modules/CatalogueRegistration.lean`: an object row `obj.modules.integers_mod` next to `obj.modules.regular` (`:457`), `ModuleCat.of ℤ (ZMod n)`, with its written form | `Sem/Modules/LinearMapsTests.lean` | T338, Modules V1 (T224) |
| FR-044 | #223 | `Sem/Algebra/Differentials.lean`: a morphism row `mor.modules.polynomial_derivative` next to `mor.sets.polynomial_derivative` (`:172`), declared by `Polynomial.derivative` as a linear map, with the theorem that its underlying map is the set map | `Sem/Modules/LinearMapsTests.lean` | T339, Modules V1 (T224) |
| FR-045 | #224 | `Sem/Foundation/Catalogue.lean`: object rows `obj.enumerated_sets.naturals`, `obj.enumerated_sets.integers` and `obj.enumerated_sets.rationals` of `cat.enumerated_sets` (`:13`) with `Denumerable.ofNat`; the morphism `mor.sets.enumeration_at` $k \mapsto X[k]$; the progressions of FR-018 as objects | a new `Sem/Foundation/EnumeratedSetsTests.lean` | T340, Enumerated sets V1 (T250) |
| FR-046 | #225 | `Sem/Modules/Operations.lean`: an object row `obj.ideals.principal` of `cat.ideals_r` (`:53`, `:154-156`) declared by `Ideal.span {a}`, with its written form `(a)`, and the theorem $\operatorname{Ann}_{\mathbb{Z}}(\mathbb{Z}/4) = (4)$ for `fun.modules.annihilator` (`:59`) | a new `Sem/Modules/IdealTests.lean` | T341, Ideals V1 (T252) |

The row identifiers of this table are the catalogue IDs of the rows; the leaves specs of
lean-cas-dsl-leaves name them.

## Catalogue defects recorded in COMPLAINTS.md (FR-047 to FR-052)

Read at `a3a66fba`. Each task starts from the source at its revision and closes its COMPLAINTS.md
entry with its evidence (LC-05, "On resolution").

| Requirement | Entry | Files and rows | Test module |
| --- | --- | --- | --- |
| FR-052 | #95, two test modules outside the build | `Catalogue.lean` imports `Sem/Foundation/{PowerSetsTests,FiniteOrdersTests}.lean`; the rows they report are repaired | the two modules |
| FR-047 | Catalogue review of bd31fe3, item 1 | every catalogue declaration with a binder `(X : Type …) [inst]`: at `a3a66fba` `Sem/Algebra/Automorphisms.lean` (`actionHom`), `Sem/Lattices/Valued/CatalogueRegistration.lean` and `Property.lean` (`(R : Type u) [CommRing R]` family parameters), and the rows of the entry still of that shape | `Sem/BinderTests.lean` |
| FR-048 | Catalogue rows in violation of LC-13, LC-14 and LC-15 | at `a3a66fba` `LinearAlgebra.companion` is defined on `monics`, no `Option`-valued row was found in `Sem/Algebra/{LinearAlgebra,FiniteSums,Calculus,Series}.lean`, and the `Fractions`, `PartialMaps` and element-literal declarations of the entry are absent; the task confirms each row of the entry at its revision and repairs any that remain | `Sem/TotalityProbes.lean` |
| FR-049 | Membership evidence (LC-18) | `Sem/Algebra/{Semirings,Units,PolynomialEvidence,LinearAlgebra,Calculus}.lean` | `Sem/EvidenceTests.lean`, `Sem/PolynomialContractTests.lean` |
| FR-050 | No registered binary product in the category of groups | `Sem/Limits/Registration.lean`: `lim.groups.product` from `Algebra/GroupProduct.lean` | `Algebra/GroupProductTests.lean` |
| FR-051 (a) | Non-inherited constructions (`Aut`, `Stab`) | `Reg/Entry.lean` (`ConstructionEntry`, method shape), `Sem/Algebra/Automorphisms.lean` | a new `Reg/GenericConstructionTests.lean` |
| FR-051 (b) | An object row cannot be identified with a functor value | `Reg/Entry.lean` (`ObjectFunctorPresentation`), `Sem/Algebra/Units.lean` | `Sem/UnitInverseTests.lean` |
| FR-051 (d) | Catalogue review of bd31fe3, item 3 | `Reg/Totality.lean` | `Sem/TotalityProbes.lean` |
| FR-051 (e) | `CONTRIBUTING.md` LC-16, the registration gate | `Reg/Semantic.lean` | `Sem/TotalityProbes.lean` |

## Structural functors of the scaffolding gaps

Each requirement adds a structural edge that the [computational milestones](https://github.com/dzackgarza/lean-cas-dsl/blob/main/specs/001-categorical-research-language/plan.md#computational-milestones) of lean-cas-dsl need: a category is implemented after the categories that its structural functors reach. The V3 category tasks of the kernel task list are added when the kernel classification (kernel T141, T143) records the classified statements; each upstream task stands before its first consumer. Line numbers are of `main` at `f009120`. Each row adds its test cases to the new test module `Reg/ScaffoldingReachTests.lean`, which asserts that the category reaches `cat.sets` along structural edges.

| Requirement | Issue | Files and rows | Consumer (lean-cas-dsl) |
| --- | --- | --- | --- |
| FR-022 | #201 | `Sem/Exceptional/CatalogueRegistration.lean`: `cat.crystals` with a non-opaque expression; a structural functor row to `cat.sets` declared by `crystalsToSets` (`Exceptional/Mathlib.lean:153`); delete `oport.crystals.sets` | T225, before the V3 task of `cat.crystals` |
| FR-023 | #202 | `Sem/Foundation/`: `cat.topological_spaces` (Mathlib `TopCat`) with its structural forget; `Sem/Algebra/Schemes.lean`: structural `fun.schemes.space` declared by `Scheme.forgetToTop` | T226, before the V3 task of `cat.schemes` |
| FR-024 | #203 | `Sem/Modules/Operations.lean`: structural functor from `cat.ideals_r` to `cat.subobjects_modules_r` at the regular module | T227, before Ideals V1 (T252) |
| FR-025 | #204 | `Reg/Semantic.lean` `SemanticState.structuralEdges` (`:1680-1693`): derive `refine(B, c) → B`; the immediate-functor validation (`validateImmediateFunctor`) refuses a row equal to it | T228, before the V3 task of the first refined category of forms over rings |
| FR-026 | #205 | `Sem/FibrationRegistration.lean`: structural `fun.bilin_forms.module` from `cat.bilin_forms_over_rings` to `cat.modules_over_rings_ext` | T229, before the V3 task of `cat.bilin_forms_over_rings` |
| FR-027 | #206 | `Sem/QuadFibrationRegistration.lean`: structural `fun.quad_forms.module` to `cat.modules_over_rings_ext` | T230, before the V3 task of `cat.quad_forms_over_rings` |
| FR-028 | #207 | `Sem/FibrationRegistration.lean`: structural functor from `cat.modules_over_rings_ext` to `cat.modules_total` over $\mathbf{CRing} \to \mathbf{Ring}$, with the commuting theorem for the two projections | T231, before the V3 task of `cat.modules_over_rings_ext` |
| FR-029 | #208 | `Lattices/Valued/Cusps.lean`: structural functor from `cat.cusps` to `cat.integral_lattice`, declared by `CuspObject.lattice` | T232, before the V3 task of `cat.cusps` |
| FR-030 | #209 | `Sem/Lattices/Valued/CatalogueRegistration.lean`: structural rows for `definiteForget`, `indefiniteForget` (`Lattices/Valued/DefiniteIndefinite.lean:46`, `:57`) into `cat.finite_projective_lattice` at $(\mathbb{Z}, \mathbb{Z})$ | T233, before the V3 tasks of `cat.definite_lattice` and `cat.indefinite_lattice` |
| FR-031 | #210 | `Sem/Lattices/Valued/CatalogueRegistration.lean`: structural rows for the inclusions of `cat.finite_free_lattice` (`Lattices/Valued/Arithmetic.lean:40-46`), `cat.even_lattice` (`ScaleAndEvenness.lean:265`) and `cat.unimodular_lattice` (`MetricDual.lean:166`) | T234, before the V3 tasks of the finite free, even and unimodular lattice families |

## Project Structure

### Documentation (this feature)

```text
specs/001-catalogue-inputs-for-the-cas/
├── plan.md
├── spec.md
├── research.md
├── data-model.md
├── quickstart.md
├── contracts/registry-additions.md
├── checklists/requirements.md
└── tasks.md
```

### Source Code (repository root)

```text
LeanCategories/
├── Catalogue/
│   ├── Registry/        # schema (Entry, Computation), validators (Semantic), tests and probes
│   ├── Semantics/       # rows: Algebra/, Foundation/, Modules/, Lattices/, ConstructorRegistration
│   ├── Holds.lean       # classifier inhabitation and refinement
│   └── Constructors.lean
├── Foundation/          # Sets, Subsets, WellOrderedSets
├── Modules/             # TruncatedResolutions, Bilinear/Valued
├── ForMathlib/          # notions that Mathlib lacks (unbounded semilattice categories)
└── All.lean             # imports every module with a row
```

**Structure Decision**: the existing library layout. Rows stay with the module of their
mathematics; schema changes are in `Catalogue/Registry/`.

## Complexity Tracking

No constitution violation is justified.

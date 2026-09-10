---
title: "Sage preamble definition catalogue"
---

Source: `~/research/src/dzack_research/preamble` — every non-checkpoint `.sage` file (~30,000 lines across 80 files) read completely, 2026-08-14.

This is the theory-ingestion inventory of the Sage research preamble: every category, functor, axiom, construction, and distinguished object it names, recorded as formalization targets for `lean-categories`. How the preamble constructs a notion in Sage is deliberately not recorded. The Sage formulation is sometimes loose or wrong; each such defect carries a ⚠ flag so the formalization fixes it rather than transcribing it, and the corrected definitions eventually flow back down to Sage. Flags marked (source) are admitted in the preamble's own comments; (inferred) is extraction-time analysis.

A checkbox is a term to route through the reuse gate in `AGENTS.md`: close it when the notion has a principled owner in this repository, pinned Mathlib, or a registered external formalization. The active work queue is `TODO.md`; the corpus-wide foundation is governed by `PLAN-FOUNDATIONAL-CORPUS-CATALOGUE-SWEEP`, `PLAN-FOUNDATIONAL-CORPUS-DEFINITION-SWEEP`, and `PLAN-FOUNDATIONAL-CORPUS-THEOREM-SWEEP`. This Sage catalogue is supplementary source material unless admitted to the frozen foundational corpus.

## Systemic defects the formalization must fix

Nine patterns recur across every subtree. They, not the individual notions, are the real distance between the preamble and the intended mathematics.

1. **Almost nothing is a functor.** Dual, discriminant, twist, orthogonal sum, `O(L)`, invariants/coinvariants, forget-form/forget-action, and the 21 `Cat` constructions are all object-level methods with no morphism action. Honest functors exist only in `categories/functors/` (module/algebra base change, free/forgetful with adjunction data, ring center on the core, trivial action) — and even there no functor law, naturality square, or triangle identity is ever checked.
2. **Framings are baked into object identity.** Chosen generating sets, relation tuples, generator orders, and Gram matrices participate in equality and hashing; symmetry, decomposability, and integrality are matrix conditions in the chosen framing while the docstrings claim the basis-free reading.
3. **Axioms are self-reports.** The refine mechanism admits an object when it answers `True` to a certifying predicate; predicates in the pure strata return `True` by placement; no universal property is checked anywhere — products, kernels, cones, biproducts are declared by handing over structure morphisms.
4. **Morphism structure is declared, not carried.** Algebra maps are module maps, ring maps are set maps, Galois characters and restriction maps have no evaluation, inclusions live in `Sets()`, and equivariance checking defaults off.
5. **Isomorphism versus equality is handled cleanly in exactly one place** — `Isomorphism` as a property of an arrow, and cached functors making `F(dom f)` *be* the domain of `F(f)` — and conflated elsewhere (dual-frame identification, matrix-equals-morphism, Gram-equality specimen naming).
6. **Sign and value conventions drift.** Positive- and negative-definite ADE circulate under one name; signed and unsigned discriminant under one word; `q(x)` is the bilinear self-pairing, not `½⟨x,x⟩`; Nikulin's `ℚ/2ℤ` halving is baked into value modules; "coinvariants" names two different objects.
7. **ℤ-hard-wiring.** Categories declared over a general base admit only ℤ or fields in practice: integral solving, torsion forms, group lattices, presented modules, fraction-field quotients.
8. **Finiteness leaks.** `GroupAction` requires finite `G` while group-lattice files promise infinite-order isometries; adjunction counits and forgetful morphism actions enumerate underlying sets; subgroup closure is capped by a constant.
9. **Outright errors that must not be imported:** `ℵ₁ := continuum` (the continuum hypothesis baked into the cardinal vocabulary); restriction of scalars returning the free module on the same generators; `involute` (the symmetrization, not an involution); `is_abelian` for absolute Galois groups (wrong in positive characteristic); Γ grouped as a free-algebra left adjoint; the genus branch of `is_isometric` without Eichler's hypotheses.

## Organizing layers

**`catalogue.sage`** — registry of named integral lattices in the negative-definite root convention; two classification tables — Nikulin's 75 even indefinite 2-elementary lattices of signature (1, r−1) keyed by (r, a, δ), and Alexeev–Engel Table 2 of even negative-definite 2-elementary lattices at 1-cusps (several isometry classes per key, some glued along totally isotropic discriminant subgroups); three named involutions of Λ_K3 = U³ ⊕ E8²; the embedding chain T_Co ↪ T_En ↪ T_dP ↪ Λ_K3 with T_En, T_dP as coinvariant lattices of two involutions.

**`refine.sage`** — the axiom mechanism: placement of an object in a category demands the declared abstract data (structure) and a `True` answer from each certifying predicate (axioms). An axiom is an object's self-report; placement never grants a property. Nothing about morphisms, composition, or functoriality is enforced.

**`sterk.sage`** — transcription of Sterk's classification of the five 0-cusps of the Baily–Borel compactification of degree-2 polarized Enriques moduli, as O-orbits of primitive isotropic vectors in T_En = U ⊕ U(2) ⊕ E8(2), each with a root configuration (norms −2/−4) whose Coxeter diagram is the cusp diagram. No orbit computation, no inequivalence proof.

## Sets, cardinals, abstract categories, functors

Source files: `catalogue.sage`, `refine.sage`, `sterk.sage`, `init.sage`, `abstract_categories/{cat,arrow_categories,slice_categories,products}.sage`, `sets/sets.sage`, `functors/*.sage`.

### Sets and cardinals

- [x] **Sets (owned)** with axioms **Finite / Countable / Infinite / Uncountable / TotallyOrdered** ⚠ Countable = chosen enumeration data (source is explicit); TotallyOrdered carried as structure, not placement — the file's own statement of the axiom-vs-structure distinction
  - Mathlib: `Set.Finite` — `Mathlib/Data/Set/Finite/Basic.lean`
  - Mathlib: `Set.Infinite` — `Mathlib/Data/Set/Finite/Basic.lean`
  - Mathlib: `Set.Countable` — `Mathlib/Data/Set/Countable.lean`
  - Mathlib: `Uncountable` — `Mathlib/Data/Countable/Defs.lean`
  - Mathlib: `IsTotal` — `Mathlib/Order/Defs/Unbundled.lean`
- [ ] **ConditionSet / ImageSet / PowerSet / SubsetsOfSize / FiniteSubsets** — subset, image (with optional declared injectivity), power set, k-subsets, finite subsets
- [x] **ordered sets; Δ[n]** — the standard finite ordered sets, Δ[ℵ₀] = ℕ ⚠ "simplex indexing objects" with no face/degeneracy maps: Δ is not a category here
  - Mathlib: `SimplexCategory` — `Mathlib/AlgebraicTopology/SimplexCategory/Defs.lean`
- [x] **Cardinals ℵ_n** ⚠ `ℵ₁ = continuum` hard-codes the continuum hypothesis into the vocabulary — the most consequential error found
  - Mathlib: `Cardinal.aleph` — `Mathlib/SetTheory/Cardinal/Aleph.lean`

### Abstract categories (Cat, arrows, slices, (co)limits)

- [x] **Cat** — category of categories ⚠ no morphisms: no functors between categories are ever constructed; its 21 constructions are installed on every category, bypassing the refine discipline
  - Mathlib: `Cat` — `Mathlib/CategoryTheory/Category/Cat.lean`
- [x] **ArrowCategory Ar(C)** — objects = morphisms, morphisms = commuting squares ⚠ the squares are never constructed (only an `is_commuting_square` predicate on generators); dom/cod functors named, absent
  - Mathlib: `Arrow` — `Mathlib/CategoryTheory/Comma/Arrow.lean`
- [x] **IsoArrowCategory; Core(C)** — declared-isomorphism arrows; maximal subgroupoid ⚠ core's fewer-arrows nature unexpressible in the object-based subcategory relation; `is_isomorphism` true by placement
  - Mathlib: `Core` — `Mathlib/CategoryTheory/Core.lean`
- [x] **Isomorphism(f, g)** — invertibility declared with both round trips checked on generators; iso as a property of the arrow, not the objects (the clean separation in these files) ⚠ only for objects with a sole structure-generating family
  - Mathlib: `Iso` — `Mathlib/CategoryTheory/Iso.lean`
- [ ] **Ar(X,Y) / IsoAr(X,Y)** ⚠ Aut-torsor structure claimed, not implemented
- [x] **SliceOver C/X; CosliceUnder X\C** ⚠ declared subcategories of C (false: the relation is a forgetful functor); no triangle morphisms defined ⚠ Slice mutates the domain in place: (A, f) conflated with A, one slice at a time
  - Mathlib: `Over` — `Mathlib/CategoryTheory/Comma/Over/Basic.lean`
  - Mathlib: `Under` — `Mathlib/CategoryTheory/Comma/Over/Basic.lean`
- [ ] **SubObject / SuperObject / CoveringObject / CoveredObject** — mono/epi-represented slices ⚠ `is_epi` is an unchecked flag
- [x] **Kernel / Cokernel categories** ⚠ parameterized by f, universal property never constructed or checked
  - Mathlib: `HasKernel` — `Mathlib/CategoryTheory/Limits/Shapes/Kernels.lean`
  - Mathlib: `kernel` — `Mathlib/CategoryTheory/Limits/Shapes/Kernels.lean`
  - Mathlib: `cokernel` — `Mathlib/CategoryTheory/Limits/Shapes/Kernels.lean`
- [ ] **DiagramCategory / DirectedSystem / InverseSystem** ⚠ no index category, no order consulted, no cocycle compatibility
- [x] **Cone / Cocone / Product / Coproduct / Biproduct / DirectSum** ⚠ no universal property checked anywhere; cones don't commute with transitions; biproduct relation π_j ι_i = δ_ij stated, unchecked; Cone declared subcategory of DirectedSystem (false containment)
  - Mathlib: `Cone` — `Mathlib/CategoryTheory/Limits/Cones.lean`
  - Mathlib: `Cocone` — `Mathlib/CategoryTheory/Limits/Cones.lean`
  - Mathlib: `HasProduct` — `Mathlib/CategoryTheory/Limits/Shapes/Products.lean`
  - Mathlib: `HasCoproduct` — `Mathlib/CategoryTheory/Limits/Shapes/Products.lean`
  - Mathlib: `HasBiproduct` — `Mathlib/CategoryTheory/Limits/Shapes/Biproducts.lean`
  - Mathlib: `DirectSum` — `Mathlib/Algebra/DirectSum/Basic.lean`
- [ ] **CartesianProductOfSets** vs module biproduct — explicitly distinguished; the sharpest correct distinction in these files (conflating them makes ⊗'s universal property unstatable)
- [x] **TensorProductCategory** — M ⊗ N as a cocone under U(M) × U(N) with the universal bilinear map as structure morphism (correct: no canonical M → M⊗N, no projections); **from_bilinear** — the unique factorization ⚠ bilinearity of the input never checked; only binary, generator-ordering-dependent
  - Mathlib: `TensorProduct` — `Mathlib/LinearAlgebra/TensorProduct/Defs.lean`

### Functors (the only honest ones in the preamble)

- [ ] **AlgebraBaseChangeFunctor** − ⊗_R S : Alg(R) → Alg(S) — honest (object + morphism action) ⚠ computed by carrying presentations, never via the universal property; no functor law checked anywhere in the package
- [x] **BaseChangeFunctor** − ⊗_R S : Mod(R) → Mod(S); **fraction_field_base_change** (rationalization) ⚠ implemented only for modules free on their framing
  - Mathlib: `ModuleCat.extendScalars` — `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean` (line 400)
- [x] **RestrictionOfScalarsFunctor** ⚠ object-level only, and the object action returns the free R-module on the same generators — not restriction of scalars; docstring and implementation contradict each other
  - Mathlib: `RestrictScalars` — `Mathlib/Algebra/Algebra/RestrictScalars.lean`
- [x] **BaseChangeAdjunction F ⊣ G** with unit m ↦ m ⊗ 1 ⚠ stated over the broken G; triangle identities and naturality never checked; hom-set bijections left abstract
  - Mathlib: `ModuleCat.extendRestrictScalarsAdj` — `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean` (line 884)
- [x] **FreeModuleFunctorClass F_R : Set → Mod(R)** — honest; cached so F(dom f) *is* the domain of F(f) (the one place equality-vs-isomorphism is enforced)
  - Mathlib: `ModuleCat.free` — `Mathlib/Algebra/Category/ModuleCat/Adjunctions.lean`
- [x] **UnderlyingSetOfGroupFunctor U : Grp → Set** — honest
  - Mathlib: `GrpCat` — `Mathlib/Algebra/Category/Grp/Basic.lean`
- [x] **ForgetfulFunctorClass U : Mod(R) → Set** — honest ⚠ morphism action enumerates the underlying set: unconstructible for infinite modules
  - Mathlib: `forget (ModuleCat.{u} R)` — `Mathlib/Algebra/Category/ModuleCat/Adjunctions.lean`
- [x] **FreeForgetfulAdjunction F_R ⊣ U** — unit, counit, both hom-set bijections implemented ⚠ counit enumerates U(M): finite modules only; triangle identities stated in prose, never represented
  - Mathlib: `ModuleCat.adj` — `Mathlib/Algebra/Category/ModuleCat/Adjunctions.lean`
- [x] **TensorAlgebraFunctor / SymmetricAlgebraFunctor / AlternatingAlgebraFunctor** — honest, with correct adjoint targets (algebras / commutative / graded-commutative) ⚠ **DividedPowerAlgebraFunctor** grouped with them under one "free algebra functor" and one shared unit: Γ is not left adjoint to any forgetful functor to modules
  - Mathlib: `TensorAlgebra` — `Mathlib/LinearAlgebra/TensorAlgebra/Basic.lean`
  - Mathlib: `SymmetricAlgebra` — `Mathlib/LinearAlgebra/SymmetricAlgebra/Basic.lean`
  - Mathlib: `ExteriorAlgebra` — `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean`
- [x] **GroupRingFunctor R[−]** ⚠ object-level only (no R[G] → R[H]); codomain declared Rings while the construction is an R-algebra
  - Mathlib: `MonoidAlgebra` — `Mathlib/Algebra/MonoidAlgebra/Defs.lean`
- [ ] **FreeModuleOnGroupFunctor** = F_R ∘ U — honest; correctly distinguished from R[G]
- [x] **RingCenterFunctor Z : core(Rings) → CRings** — honest; source is the core precisely because Z is not functorial on general ring maps (explicit counterexample recorded: ℚ[t] → Λ, t ↦ e₁) ⚠ codomain inconsistent between object and morphism halves
  - Mathlib: `Subring.center` — `Mathlib/Algebra/Ring/Subring/Basic.lean`
- [ ] **TrivialActionFunctor ε* : Lat → Lat_G** — honest, cached ⚠ enumerates G (finite groups only); the double adjunction (−)_G ⊣ ε* ⊣ (−)^G is named in the docstring and neither adjoint is constructed — so the invariant/coinvariant lattices used by the catalogue are not obtained as adjoint values

### Catalogue specimens and distinguished data

- [ ] **Named lattices** — 0, ⟨1⟩, ⟨2⟩, U/H, U(2), ADE (A1–A21, D2–D22, E6, E7, E8, negative definite), E8(2), E10 = U ⊕ E8, E10(2), I_{p,q}, Λ_K3 = U³ ⊕ E8² (named generators), Λ_K3 degree variants ⟨−2d⟩ ⊕ U² ⊕ E8², T_En = U ⊕ E10(2) (sig (2,10)), T_dP = U ⊕ U(2) ⊕ E8² (sig (2,18)), T_Co and S_Co Coble lattices, S_dP = U(2), S_En = E10(2), Nikulin ± eigenlattices ⚠ (r,a,δ) notation reused across two indexing conventions; D3 ≅ A3 double-registered; table keys conflate isometry class with one chosen Gram presentation; glue rows fix lattices only up to isometry with the gluing subgroup not table data
- [ ] **Nikulin (r,a,δ) tables** — the 75-entry indefinite table; the Alexeev–Engel negative-definite table ⚠ uniqueness certificates (signature + invariants verification) never performed
- [ ] **Involutions I_dP, I_En, I_Nik of Λ_K3** ⚠ isometry and order-2 never checked; defined relative to one chosen decomposition and summand order
- [ ] **Embeddings** — E8(2) ↪ T_dP diagonal (AEGS), T_Co ↪ T_En, T_En ↪ T_dP, T_En/T_dP ↪ Λ_K3 as coinvariant lattices ⚠ named "primitive embeddings"; primitivity never checked; produced as lattices, not arrows
- [ ] **Sterk cusp data** — five primitive isotropic vectors in T_En (isotropy checked, primitivity not); five root configurations (sizes 12, 10, 12, 11, 14; norms −2/−4 mixed without record); reflection s_{v22}; rooted Coxeter diagrams of the five cusps ⚠ `involute` is the symmetrization x + s(x), not an involution; no O-orbit inequivalence anywhere; two coordinate presentations of configurations 1–3 with no comparison map
- [ ] **refine mechanism** — certifying predicates + abstract-data obligations as the axiom system ⚠ axioms are self-reports; obligations checked by attribute presence; morphism placement explicitly not recorded

## Rings, algebras, number fields

Source files: `categories/algebras/{algebras,free_algebras,finitely_presented_algebras,framed_free_algebras,number_fields}.sage`, `categories/rings/{rings,predicate_subrings}.sage`.

### Categories

- [x] **OwnedSemirings / OwnedRngs / OwnedRings / OwnedDivisionRings / OwnedFields** — the ring tower (semiring = mult. monoid over add. comm. monoid; rng; unital ring as the join; division ring; field)
  - Mathlib: `Semiring` — `Mathlib/Algebra/Ring/Defs.lean`
  - Mathlib: `NonUnitalRing` — `Mathlib/Algebra/Ring/Defs.lean`
  - Mathlib: `Ring` — `Mathlib/Algebra/Ring/Defs.lean`
  - Mathlib: `DivisionRing` — `Mathlib/Algebra/Field/Defs.lean`
  - Mathlib: `Field` — `Mathlib/Algebra/Field/Defs.lean`
- [x] **Algebras(R)** — associative unital R-algebras; defining datum the structure map R → Z(A) ⚠ no morphism side at all; membership decided by coercion, weaker than the declared structure map
  - Mathlib: `Algebra` — `Mathlib/Algebra/Algebra/Defs.lean`
- [ ] **FramedAlgebras(R)** — algebras with a declared surjection FreeAlg_R(S) ↠ A; obligation: `product_on_algebra_generators` ⚠ the surjection never constructed or checked
- [ ] **FreeAlgebras(R)** ⚠ conflates free-as-module with free object in R-Alg; **GradedFreeAlgebras(R)** — shared graded structure of T, Sym, Λ, Γ
- [x] **TensorAlgebras / SymmetricAlgebras / AlternatingAlgebras / DividedPowerAlgebras** (R) — the four flavors; Γ stated via the universal property Hom(Γ²M, W) ≅ quadratic maps ⚠ documented, never constructed; Λ never declared graded-commutative
  - Mathlib: `TensorAlgebra` — `Mathlib/LinearAlgebra/TensorAlgebra/Basic.lean`
  - Mathlib: `SymmetricAlgebra` — `Mathlib/LinearAlgebra/SymmetricAlgebra/Basic.lean`
  - Mathlib: `ExteriorAlgebra` — `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean`
  - Mathlib: `DividedPowerAlgebra` — `Mathlib/RingTheory/DividedPowerAlgebra/Init.lean`
- [ ] **FinitelyPresentedAlgebras(R); FramedFGAlgebras(R)** ⚠ finiteness of the generating set unenforced
- [x] **OwnedNumberFields()** — K = ℚ[x]/(f), f irreducible, presented on a primitive element; irreducibility asserted at construction, then placed in fields
  - Mathlib: `NumberField` — `Mathlib/NumberTheory/NumberField/Basic.lean`

### Axioms / predicate flags

- [ ] `is_algebra`, `is_free`, `is_finitely_presented` ⚠ all return True unconditionally by placement
- [x] **Structure-map obligation** `_ring_morphism_defining_algebra_structure` : R → Z(A) ⚠ implementations land in Hom(R, A) or are set maps in Rings() homsets; centrality "trusted where it cannot be decided"
  - Mathlib: `Algebra` — `Mathlib/Algebra/Algebra/Defs.lean`

### Monomial systems (the mathematical core)

- [ ] **MonomialSystem** — (what a monomial is, what two multiply to), stated once for T/Sym/Λ/Γ; products return (scalar, monomial) because x∧y = −y∧x and γ_aγ_b = C(a+b,a)γ_{a+b} are not monoid operations
- [ ] **WordMonomials** (T = R⟨S⟩); **CommutativeMonomials** (Sym = R[S]); **AlternatingMonomials** (Λ; zero on overlap, shuffle sign) ⚠ sign fixed by an ambient order on S that is not part of the data; **DividedMonomials** (Γ; binomial product; ≅ Sym over ℚ via γ_a = s^a/a!, not over ℤ — why Γ² and not Sym² classifies quadratic forms)

### Constructions

- [x] **FreeAlgebraOnSet FreeAlg_R(S)** — free on Mon(S) as a module, free on S as an algebra, both framings carried
  - Mathlib: `FreeAlgebra` — `Mathlib/Algebra/FreeAlgebra.lean`
- [x] **hom (universal property)** — Hom_{R-Alg}(FreeAlg_R(S), A) ≅ Hom_Set(S, U(A)) ⚠ produced arrow is a ModuleMorphism; multiplicativity never a checked law
  - Mathlib: `FreeAlgebra.lift` — `Mathlib/Algebra/FreeAlgebra.lean`
- [ ] **induced_hom** — FreeAlg_R(g) for g : S → T (the free construction's morphism action) ⚠ functor laws stated nowhere
- [ ] **graded_piece(n)** — the degree-n free submodule ⚠ inclusion's injectivity stamped, not proven
- [ ] **ideal_generators_in_degree** — ⟨K⟩_n = Σ A_i K A_j (left-adjoint compatibility of quotients) ⚠ one two-sided formula for all flavors
- [x] **γ_a(x) divided powers; divided_square γ₂(x)** — the operation quadratic forms are built from
  - Mathlib: `dpow` — `Mathlib/RingTheory/DividedPowers/SubDPIdeal.lean`
- [ ] **Comparison morphisms** — T ↠ Sym, T ↠ Λ, Sym → Γ (x^n ↦ n!γ_n), Γ → Sym over ℚ only
- [ ] **Adjunction extensions** — tensor_extension / symmetric_extension / alternating_extension (alternating condition genuinely verified) / divided_power_extension; **divided_power_induced_morphism Γ(f)** ⚠ based modules only
- [ ] **FinitelyPresentedAlgebra F/I; FGAlgebra** — presentation data (F, I, chosen relations) bound to the quotient ⚠ chosen relation generators are part of object identity: two presentations of one algebra are unrelated objects
- [ ] **base_change (algebras)** ⚠ object-level; monomial route defined only for the symmetric flavor
- [ ] **FreeAlgebraIdeal with normal form** ⚠ symmetric flavor only (no normal form for two-sided ideals of T)
- [ ] **PresentedFreeAlgebra A(F)/⟨K⟩** — graded algebras of non-free presented modules ⚠ flavor is a string tag; the quotient never actually formed; equality decided degree-by-degree
- [x] **polynomial arithmetic surface** — quo_rem/gcd/xgcd/factor/roots/discriminant/resultant/derivative via the polynomial presentation ⚠ symmetric-flavor methods inherited by T, Λ, Γ where they are wrong or undefined; `subs` raises images to powers, wrong for Γ; `is_integral_domain` inherited by Λ where false
  - Mathlib: `Polynomial` — `Mathlib/Algebra/Polynomial/Basic.lean`
- [ ] **rank-one specializations** — leading coefficient/monic/roots only at rank one (no monomial order is chosen above rank one — deliberate)

### Number fields

- [ ] **own_number_field(f)** — ℚ[x]/(f) as finitely presented algebra refined into fields; **defining_polynomial / degree / primitive_element**
- [ ] **discriminant d_K** (of the maximal order, explicitly ≠ disc(f)); **signature (r,s)**; **class_number**; **ramified_primes**
- [x] **is_galois / galois_group** ⚠ returns the group of the defining polynomial — the normal closure's group when K/ℚ is not normal; one method, two different groups
  - Mathlib: `IsGalois` — `Mathlib/FieldTheory/Galois/Basic.lean` (line 58); `Polynomial.Gal` — `Mathlib/FieldTheory/PolynomialGaloisGroup.lean` (line 55)
- [ ] **underlying_algebra(R)** — an R-form with the same presentation (explicitly *an* R-form, not the maximal order); **base_change_functor** − ⊗_R Frac(R) — a genuine functor object (the file's own reason: a method call is not an arrow)
- [x] **integral_basis** ⚠ returns the power basis of ℤ[α], not of 𝒪_K, whenever the index is nontrivial; disconnected from `ring_of_integers` (engine's maximal order) — two incompatible integral structures
  - Mathlib: `integralBasis` — `Mathlib/NumberTheory/NumberField/Basic.lean` (line 394)
- [ ] **element theory** — multiplication endomorphism matrix; norm/trace/char.poly/min.poly (presentation-independent); is_integral (monic min.poly over ℤ, not membership in ℤ[α]); inverse via Bézout; conjugates/embedding_images (roots of f)

### Rings infrastructure

- [x] **ring_center Z(R)** — R itself when commutative, else a predicate carve-out ⚠ cached "because Z is a functor", but only the object assignment exists (and Z isn't functorial on ring maps anyway — see RingCenterFunctor)
  - Mathlib: `Subring.center` — `Mathlib/Algebra/Ring/Subring/Basic.lean`
- [x] **is_central** — decided against a finite algebra generating set (centralizer is a subring)
  - Mathlib: `Algebra.IsCentral` — `Mathlib/Algebra/Central/Defs.lean` (line 67)
- [ ] **R^n** — the free module on the canonical framing, on the whole ring tower
- [x] **PredicateSubring {z : P(z)}** — subrings by membership predicate (center, centralizer, fixed ring, integral closure named as intended instances); deliberately non-enumerable ⚠ closure under operations never verified; inclusion is a set map; equality by description *string*
  - Mathlib: `Subring` — `Mathlib/Algebra/Ring/Subring/Defs.lean`
- [ ] **OwnedRing / engine boundary** — one owned facade per Sage ring; ℤ ℚ ℝ ℂ owned; R[names] = free algebra; R/𝔞 quotients (ℚ/ℤ, ℚ/2ℤ); fraction_field; ring_of_integers; algebraic_closure; ideals; embeddings ⚠ inexact rings refined Uncountable from a computational property; OwnedRingMap deliberately category-free (nothing records ring-map-ness)

## Groups, profinite and Galois theory

Source files: `categories/group/{groups,finitely_presented_groups,predicate_subgroups}.sage`, `categories/group/profinite/*.sage`.

### Categories

- [ ] **OwnedGroups** ⚠ only super-category is Sets(): no group axiom imposed anywhere in the tower; **OwnedFinitelyGeneratedGroups**; **OwnedFinitelyPresentedGroups**; **OwnedFiniteGroups** (finite ⊂ f.p., correctly); **OwnedAbelianGroups** (= ℤ-Mod, super-categories [OwnedGroups, Modules(ℤ)]); **OwnedFiniteAbelianGroups**
- [ ] **GroupsWithChosenFinitePresentation** — a *chosen* presentation as data, vs the property ⚠ display name identical to the property category
- [x] **ProfiniteGroups** — inverse limits of finite groups ⚠ no inverse system, topology, compactness, or total disconnectedness modeled; plain subcategory, not an axiom
  - Mathlib: `ProfiniteGrp` — `Mathlib/Topology/Algebra/Category/ProfiniteGrp/Basic.lean` (line 44); `ProfiniteGrp.of` (line 82); `ProfiniteGrp.Hom` (line 102)
- [x] **AbsoluteGaloisGroups** — G_K = lim Gal(L/K)
  - Mathlib: `absoluteGaloisGroup` — `Mathlib/FieldTheory/AbsoluteGaloisGroup.lean` (line 43); `absoluteGaloisGroupAbelianization` (line 59)

### Constructions and predicates (discrete groups)

- [ ] **refine_group / _group_categories** — witness-based placement (finite generating set, presentation, commutativity) ⚠ short-circuits on already-placed groups, so later refinements are lost
- [ ] **three-valued predicates** is_finitely_generated / is_finite (True/False/Unknown) ⚠ "generators computable ⇒ finitely generated" non-sequitur
- [ ] **is_arithmetic_group** — ℤ-points of a linear algebraic group over ℚ, as a finite-generation witness (Borel–Harish-Chandra) ⚠ actual test is "named Sage matrix group over ℤ" — a representation proxy
- [ ] **presenting_free_group / defining_relations / _presentation_of** — presentation extraction per realization class
- [ ] **AbelianGroupEndomorphismRing End(A)** — the ring that exists because A is abelian; ℤ → End(A) from initiality (the content of Ab ≅ ℤ-Mod) ⚠ built as a set map wearing a ring-morphism label
- [x] **PredicateSubgroup {g : P(g)}** — subgroups by membership predicate (for O(L)-like cases); centralizer implemented; normalizers/stabilizers/ker(O(L) → O(A_L)) named ⚠ closure under product/inverse never checked; inclusion is a set map in Sets()
  - Mathlib: `Subgroup` — `Mathlib/Algebra/Group/Subgroup/Defs.lean`
- [ ] **notation management** — additive vs multiplicative recorded at intake
- [ ] **Groups catalogue** — C_n, S_n, A_n, D_n, dicyclic, quaternion, V₄; free/Artin/braid/Coxeter/Weyl/reflection families; classical matrix groups GL/SL/Sp/GU/SU/GO/SO; Heisenberg; sporadics; etc.

### Absolute Galois theory (the choice-management showcase)

- [x] **AbsoluteGaloisGroup** — the *based* object G_{K,K̄,ι} = Aut_{ι(K)}(K̄), explicit π₁-basepoint analogy ⚠ eq/hash use only the base field, collapsing the based structure the class exists to record
  - Mathlib: `absoluteGaloisGroup` — `Mathlib/FieldTheory/AbsoluteGaloisGroup.lean` (line 43)
- [ ] **GaloisChoicePolicy** — reproducible-not-canonical choice management; four named non-canonical choices, each a torsor: (1) K̄ under Aut(K̄) ⚠ made outside policy control; (2) base embedding ι under G_K; (2′) subfield embeddings, ambiguity a Gal-coset; (3) extension of a finite-level automorphism, torsor under Gal(M/L) (drives lazy element realization); (4) prolongation of a place, torsor D_v̄\G_K ⚠ never actually called — decomposition/inertia objects document a choice they don't make ⚠ policy equality by name string
- [ ] **AbsoluteGaloisGroupElement** — lazy automorphism of K̄: pair (finite stage L, automorphism of L), extended by forcing through finite normal extensions (Stacks 0BME) ⚠ mutates stage/action in place while hash/eq read them
- [ ] **lift / LiftCoset** — a chosen lift vs the canonical open coset g·G_L of all lifts (the choice-free counterpart)
- [ ] **restriction maps / finite_quotient** — G_K ↠ Gal(L/K) as defining coordinates of the limit ⚠ Morphism subclasses with no `_call_`: arrows that are labels, not maps ⚠ `finite_quotient` delegates to a method defined nowhere
- [ ] **open_subgroup / OpenAbsoluteGaloisSubgroup** — G_E after choosing E ↪ K̄, plus the conjugacy-class projection ⚠ a SageObject, not a group object; of the infinite Galois correspondence dictionary only index/is_normal/core exist
- [ ] **decomposition/inertia groups; FrobeniusConjugacyClass** — D_v̄, I_v̄ by finite-quotient images; Artin symbol as a conjugacy class, correctly never a global element ⚠ ramification never checked; the prime passed independently of the stored prolongation
- [ ] **cyclotomic / quadratic characters** — χ_n via K(μ_n); quadratic via K(√a) ⚠ no `_call_` (never evaluable); K(μ_n) built via a method that doesn't exist; K(√a) built from a wrong polynomial (constant 1−a over ℚ); ℓ-adic character and Kummer isomorphism stated, not constructed
- [ ] **restrict_along / extensions_along** — the two directions of j ∘ τ = σ ∘ j; subfield-as-embedding stance (a subfield is a field *with* an embedding, never set containment)
- [ ] **finite-field case** — G_{𝔽_q} ≅ Ẑ procyclic with canonical Frobenius ⚠ `frobenius()` uses x ↦ x^p not x^q; abstract-vs-topological cyclicity contradicted by gens override
- [ ] ⚠ **is_abelian**: True iff char > 0 — false (G_{𝔽_p(t)} nonabelian); **order**: Infinity uniformly, discarding countable-vs-uncountable; ****contains****: any endomorphism of K passes; topological generator streams don't terminate or aren't in G_K

## Schemes, varieties, divisors

Source files: `categories/schemes/*.sage`, `categories/divisors/*.sage`.

### Categories and axioms

- [x] **RingedSpaces** (X, 𝒪_X) ⚠ super-category Sets(); no topology or sheaf modeled anywhere; **LocallyRinged** axiom; **LocallyRingedSpaces**
  - Mathlib: `RingedSpace` — `Mathlib/Geometry/RingedSpace/Basic.lean` (line 44); `SheafedSpace` — `Mathlib/Geometry/RingedSpace/SheafedSpace.lean` (line 40); `LocallyRingedSpace` — `Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean` (line 43)
- [ ] **Schemes(S)** with axioms **Affine, Projective, QuasiAffine, QuasiProjective, Integral, Separated, FiniteType, Normal, Smooth, OpenImmersion, ClosedEmbedding** ⚠ the last two are morphism properties declared as object axioms; none of the eleven has a defining condition ⚠ base scheme identified with base ring — Spec never appears
- [ ] **AffineSpaces(S); ProjectiveSpaces(S); ClosedSubschemes(S); OpenSubschemes(S)**
- [ ] **Varieties(S)** — integral separated finite-type ⚠ the three axioms exist but are not applied; docstring-only definition; **Curves(S); Surfaces(S)**; axioms DimensionOne/Two, Toric
- [ ] **DivisorGroups** (free ℤ-modules on prime divisors); **WeilDivisorGroups**; **CartierDivisorGroups** ⚠ not under DivisorGroups, no CaDiv → WeilDiv map; **ClassGroups; PicardGroups** ⚠ definitionally identical framed quotient modules; no Pic → Cl comparison, no principal divisors, no div map, no scheme in sight

### Constructions

- [x] **structure_sheaf / underlying_space / stalk** — declared abstract ⚠ assert-false at every call
  - Mathlib: `Spec.structureSheaf` — `Mathlib/AlgebraicGeometry/StructureSheaf.lean` (line 890); `stalk` — `Mathlib/Topology/Sheaves/Stalks.lean` (line 82); `LocallyRingedSpace.toTopCat` — `Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean` (line 60)
- [ ] **SchemeMorphism** — compose, pullback (fiber product), evaluate_at (point evaluation *is* composition f ∘ p), fiber_over (preimages are fiber products) — the stated principles are right ⚠ two unrelated classes named SchemeMorphism in the tree
- [ ] **SchemePoint** — an R-point as a morphism Spec R → X (correct stance) ⚠ never initialized as a morphism, so it cannot compose
- [ ] **Subscheme / inclusion_morphism** ⚠ the inclusion — the class's one purpose — asserts false; **QuasiScheme** V(I)∖V(J) ⚠ carries neither I nor J
- [ ] **codimension** ⚠ irreducibility hypotheses ignored; computed against the ambient space, not the recorded ambient scheme
- [ ] **𝔸ⁿ, ℙⁿ constructors; hyperplanes; basic opens D(f); closed subschemes V(f₁…f_k); toric varieties from fans; curves from equations**
- [ ] **Pic(𝔸ⁿ) = 0, Cl(𝔸ⁿ) = 0, Pic(ℙⁿ) = ℤ, Cl(ℙⁿ) = ℤ** ⚠ true only over suitable bases (regular/UFD); over general S, Pic(ℙⁿ_S) ≅ Pic(S) × ℤ; 𝒪(1) not identified; Pic and Cl of ℙⁿ built as two unrelated modules with no comparison
- [ ] **arithmetic_genus / geometric_genus** ⚠ both return the same engine genus — identified exactly where they differ (singular curves)

## Modules: the pure / framed / presented strata

Source files: `categories/modules/pure/*.sage`, `categories/modules/framed/{framed_modules,framed_free_modules}.sage`, `categories/modules/framed/finitely_generated/*.sage`, `categories/modules/{direct_sum_objects,fractional_ideals,fraction_field_quotients,function_modules,graded_modules,scalar_actions}.sage`.

The stratification: **pure** categories are property-only placements (predicates true by membership, no witness); a **framing** adds exactly one datum — a declared surjection φ : F_R(S) → M; free adds injectivity of S → U(F_R(S)); based adds a total order on S (generators become coordinates); presented adds a second morphism F₁ → F₀ with the object as cokernel. Structural facts: **no forgetful functor framed → pure exists anywhere** (the relation is object-level super_categories); `FinitelyGeneratedModules` sits in pure/ but declares FramedModules as super-category (finite generation is not presentation-free here); `GradedModules` reads the framing while claiming the pure tree.

### Categories

- [x] **Modules(R)** — defining datum ρ : R → End(M) ⚠ the obligation is declared unenforceable ("cannot be a gate"); **VectorSpaces(k)** via field dispatch
  - Mathlib: `Module` — `Mathlib/Algebra/Module/Defs.lean`
- [x] **FreeModules(R); ProjectiveModules(R); TorsionModules(R)** ⚠ is_free/is_projective/is_torsion return True by placement; Free and Torsion route to Sage's Modules(R), not the owned one — ρ imposed inconsistently
  - Mathlib: `Module.Free` — `Mathlib/LinearAlgebra/FreeModule/Basic.lean`
  - Mathlib: `Module.Projective` — `Mathlib/Algebra/Module/Projective.lean`
  - Mathlib: `Module.IsTorsion` — `Mathlib/Algebra/Module/Torsion/Basic.lean`
- [ ] **FinitelyGeneratedModules(R)** ⚠ framed despite living in pure/
- [ ] **FramedModules(R)**; **FramedFreeModules(R)** (the join of free and framed); **FinitelyGeneratedFreeModules(R)** (based: ordered finite framing); **FinitelyPresentedModules(R)** ⚠ constructor asserts base ∈ {ℤ, field} though the category is declared over general R
- [ ] **FinitelyPresentedTorsionModules** — finite torsion ℤ-modules ≅ finite abelian groups by *simultaneous membership* in four categories ⚠ no forgetful functor; ℤ-only
- [x] **DirectSumObjects** — an object with a chosen ordered summand family ⚠ super-category Sets(): the decomposed module carries no additive structure; nothing verifies the family decomposes M
  - Mathlib: `DirectSum` — `Mathlib/Algebra/DirectSum/Basic.lean`
- [x] **OwnedIdeals(R)** — ideals = submodules of R ⚠ fractional ideals (submodules of Frac R) placed in the same category, name and objects disagree
  - Mathlib: `Ideal` — `Mathlib/RingTheory/Ideal/Defs.lean`
- [ ] **FractionFieldQuotients(R)** — cokernels of 𝔞 ↪ Frac(R) ⚠ ℤ-only in practice
- [x] **GradedModules(R); GradedAlgebras(R)** ⚠ grading assigned to chosen generators — grades the presentation, not the module; homogeneity of relations never required; A_iA_j ⊆ A_{i+j} stated, unimposed
  - Mathlib: `Gmodule` — `Mathlib/Algebra/Module/GradedModule.lean` (line 45); `GradedAlgebra` — `Mathlib/RingTheory/GradedAlgebra/Basic.lean` (line 170)

### Constructions

- [ ] **framing_morphism φ : F_R(S) → M**; module_generator_morphism S → U(M); linear_combination; inject_variables ⚠ position made meaningful via the framing's order
- [x] **F_R(S)** — finitely supported functions S → R; rigid (one object per (R, S)); integer framing via Δ[n−1]; **hom** by linear extension of set maps (the universal property) ⚠ no uniqueness statement
  - Mathlib: `ModuleCat.free` — `Mathlib/Algebra/Category/ModuleCat/Adjunctions.lean`
- [ ] **BasedFreeModule** — ordered finite case; coordinates in the engine's R^n; cross-parent equality False by fiat (identification must be a stated morphism — deliberate and correct)
- [x] **rank** ⚠ defined from the chosen framing; invariance never stated; **relations = empty ordered set** for free modules (empty ≠ absent — deliberate)
  - Mathlib: `Module.finrank` — `Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- [ ] **FinitelyPresentedModule** — cokernel of a map of finite free modules; elements as reduced coordinate vectors; induced framing on presenting generators
- [x] **FreeResolution** 0 ← M ← F₀ ← F₁ ← 0 over a PID ⚠ exactness never checked
  - Mathlib: `ProjectiveResolution` — `Mathlib/CategoryTheory/Preadditive/Projective/Resolution.lean`
- [ ] **hermite_form / invariant_factor_form** — isomorphisms onto reduced presentations, returned as arrows never bare matrices (the on-the-nose vs invariant-factor-model distinction is stated as load-bearing) ⚠ span preservation asserted
- [ ] **smith_form_module_generators / invariants / exponent / cardinality / rank / torsion_free_quotient** — Smith-form derived invariants ⚠ is_torsion_free True unconditionally off ℤ; cardinality ℵ₀ for any non-torsion module; exponent 1 when free
- [ ] **subobject_on / submodule** — subobject via Hermite-independent generators carried by an inclusion ⚠ dispatches on a `_form` attribute, not category membership
- [ ] **vector_space** — M ⊗_R Frac(R) via the genuine base-change functor (the one functor these files call)
- [x] **FractionalIdeal** — R-submodule of Frac(R) on a finite family; ring_as_module(R); as_submodule ⚠ equality by generating tuple ((2,3) ≠ (1) in ℤ); `__contains__` tests the union of principal ideals, not the sum (1 ∈ (2,3) reported false); inverse only for principal; Dedekind arithmetic absent
  - Mathlib: `FractionalIdeal` — `Mathlib/RingTheory/FractionalIdeal/Basic.lean` (line 83)
- [ ] **K/𝔞 quotients (ℚ/ℤ, ℚ/2ℤ)** — chain framing by [1/d_n] for a divisibility-cofinal chain (n! over ℤ); modulus; lift (explicitly a choice, no section); projection; cyclic-submodule classification (g)/(n) ≅ R/(n/g) over a PID
- [ ] **FunctionModule** — modules of functions (C^∞, L²) exercising the axioms without coordinates; three-valued membership (certified/refused/trusted) with a certification ladder (p-test, Schwartz, Minkowski, comparison, direct integral) ⚠ kind/domain are strings; no a.e.-equivalence quotient, so the L² pairing is degenerate; the promised pairing-as-morphism never constructed
- [ ] **ModuleOverRing(ρ)** — the S-module a ring map ρ : S → End(M) determines (the R[G]-module pattern); doctrine: extra structure = condition on where ρ lands ⚠ ρ never verified a ring morphism; elements indistinguishable from underlying elements; no restriction/extension functors here

# Morphism / tensor / group-module inventory (from inv-morphisms)

## `module_morphisms/module_morphisms.sage`

**Morphism representation convention (load-bearing).** A morphism is **not** a matrix. The construction datum is a set morphism `S → U(N)` from the domain's *ordered module generating set* `S` to the underlying set of the codomain; the morphism is its linear extension `f(Σ cᵢeᵢ) = Σ cᵢf(eᵢ)`. Descent is enforced by `_check_relations`: every row `r` of the domain's relation matrix must satisfy `Σ rᵢ f(eᵢ) = 0` in `N`, i.e. the map on the free cover `F_R(S)` kills the relation submodule and so descends to the presented domain. The matrix is *derived and cached*, never primary: rows are the coordinate vectors of `f(eᵢ)`, elements are row vectors, `v ↦ vA`.

- [ ] **ModuleHomset** (category/hom-object) — `Hom_R(M,N)` for framed `R`-modules over a common base ring.
- [ ] **ModuleMorphism** (construction) — linear extension of a generator-set morphism.
- [ ] **_check_relations** (axiom) — well-definedness/descent on the domain presentation. ⚠ Codomain relations never checked here (inferred).
- [ ] **_coordinate_vector** (construction) — chosen-lift coordinates. ⚠ Matrix of a morphism touching a presented module only well defined modulo codomain relation rows (source).
- [ ] **Additive structure on Hom** — pointwise. ⚠ No scalar action `r·f`: Hom is an abelian group but never an `R`-module object (source).
- [ ] **Composition; endomorphism_ring End_R(M)** — endset refined into `Rings()`; taken in R-Mod, never form-bearing (isometries do not add). ⚠ Ring axioms asserted by category placement only (inferred).
- [ ] **lift** (construction) — preimage via morphism matrix stacked with codomain relations.
- [ ] **_solve_left_integrally** — Smith normal form solve. ⚠ Hard-wired to ZZ (source).
- [ ] **kernel** — abstract module + inclusion from left nullspace. ⚠ Asserts free domain; no kernel for torsion domain (source).
- [ ] **cokernel** — `N/f(M)` as FinitelyPresentedModule presented by `f`.
- [ ] **image / image_contains** — subobject generated by generator images; membership predicate.
- [ ] **is_injective** — torsion domain: enumeration; free domain: rank comparison. ⚠ No branch for non-free non-torsion domain (source).
- [ ] **index [N : f(M)]** (invariant) — over ZZ by determinant. ⚠ Wrong (returns 1) for PIDs that are neither ZZ nor a field (inferred).
- [x] **orthogonal_complement** — left kernel of `Gram(N)·Aᵀ`. ⚠ Reads codomain Gram without asserting a form exists (source).
  - Mathlib: `orthogonal` — `Mathlib/LinearAlgebra/BilinearForm/Orthogonal.lean` (line 146); `orthogonalBilin` — `Mathlib/LinearAlgebra/SesquilinearForm/Orthogonal.lean` (line 48)
- [ ] **forget_form** (forgetful map) — strip form. ⚠ Object-level only; not a functor (source).
- [ ] **FramingMorphism** — declared epi `F_R(S) ↠ M`. ⚠ `is_surjective()` returns True unconditionally — datum, never verified (source).
- [ ] **ModuleAutomorphism** — endomorphism with unit-determinant matrix. ⚠ Freeness never asserted; determinant of a lift matrix not an invariant for presented modules (inferred). ⚠ `inverse()` hard-wires ZZ (source).
- [ ] **ModuleAutomorphismGroup Aut_R(M)** — two roles in one class: full automorphism homset AND literal finite generated subgroup. ⚠
- [ ] **_close** — BFS subgroup closure. ⚠ Finiteness decided by hard cap 100000, not a theorem (source).
- [ ] **order** (invariant) — Cardinal; ℵ₀ for non-enumerated. ⚠ Countability asserted for every R; not true in general (inferred).
- [ ] **FiniteAutomorphismSubgroup** (mixin) — shared finite-group surface of Aut(M) and O(L); distinguishes literal subgroup from image ρ(G).
- [ ] **inclusion ρ: G ↪ Aut(M)** (honest morphism) — tautological faithful representation.
- [ ] **_defining_matrix_group / _by_matrix** — GAP-backed conjugacy/character machinery. ⚠ Matrix determines automorphism only for free module in genuine basis (inferred).
- [ ] **conjugacy_classes_representatives; irreducible_characters; character; trivial_character** (invariants) — class functions of the group alone.
- [ ] **GroupActionHomset** (category) — homomorphisms `G → Aut_R(M)` in Groups().
- [ ] **_values_on_generators** (axiom+construction) — extends generator images over Cayley graph; second arrival = relation = homomorphism condition, no presentation needed.
- [ ] **GroupAction ρ** — full value table; checks ρ(1)=1, ρ(gh)=ρ(g)ρ(h). ⚠ Asserts G finite; no infinite group can carry an action — contradicts group_lattices' stated support for infinite-order isometries (source).
- [ ] **MorphismMatrix** (supporting) — deliberate non-subclass of Matrix; kernels private; documents that correlation c: L → L^∨ merely *coincides* with Gram matrix in dual framings. ⚠ `transpose()` documented as matrix of dual morphism but no dual morphism ever constructed (source).
- *(gap)* **Induction / restriction / base change of morphisms** — absent entirely. ⚠

## `tensors.sage`

- [ ] **DualModule M* = Hom_R(M,R)** — from presentation by left exactness. ⚠ Dual frame silently identifies F_M* with F_M via labels (source). ⚠ Object-level only; no dual of a morphism; not a functor (source).
- [ ] **TensorProductModule M ⊗_R N** — standard right-exact presentation. ⚠ No bimodule structure anywhere; symmetric-monoidal over commutative R, sides never named (source). ⚠ No f ⊗ g (source).
- [ ] **Tensor T^{p,q}(M)** (parent) — type-(p,q) tensors as `(M^{⊗p}) ⊗ (M*^{⊗q})`. ⚠ Identification with multilinear maps needs f.g. projective; stated, never checked (source).
- [ ] **valence (p,q) / degree** (invariants).
- [ ] **TensorElement** — components in a framing backed by intrinsic element. ⚠ `__eq__` without `__hash__` (inferred).
- [ ] **Evaluation / contract / trace / tensor_product (outer)** (constructions) — partial contraction; slot pairing; self-contraction; concatenation.
- [ ] **raise_index / lower_index** — musical isomorphisms. ⚠ raise asserts integral inverse Gram = unimodularity required (source). ⚠ Slot positions not inverse to each other (inferred).
- [ ] **base_changed** — componentwise scalar extension. ⚠ No flatness/compatibility statement (inferred).
- [ ] **MixedTensorAlgebra T(M) ⊗ T(M*)** — bigraded algebra, outer product multiplication. ⚠ Associativity/bigrading asserted only (inferred).
- [ ] **structure morphism ρ: R → End(−)** as module/algebra structure. ⚠ Declared in Rings() while target endset never refined into Rings() (source).
- [ ] **Gram matrix as type-(0,2) tensor; multiplication table as type-(1,2)** (distinguished).
- [ ] **tensor(...) constructor; zero; one**.

## `group_modules/group_modules.sage`

- [ ] **GroupModules(R, G)** (category) — stated "R[G]-modules"; objects (M, ρ), morphisms equivariant R-linear. ⚠ super_categories forces f.g. FREE underlying module: actually the category of G-lattices over R, not R[G]-Mod (source). ⚠ Docstring claims no finiteness on G but everything requires G finite (source). ⚠ R[G] itself never constructed (inferred).
- [ ] **is_semisimple** (axiom, Maschke) — R field and |G| invertible.
- [ ] **splitting_field K** (distinguished, Brauer) — Q(ζ_{|G|}). ⚠ Uses order not exponent (source).
- [ ] **is_split** (predicate) — Frac(R) ⊇ K.
- [ ] **GroupModule (M, ρ)** (construction) — identity is the pair.
- [ ] **forget_action** (forgetful map) — ⚠ object/element-level only; not a functor (source).
- [ ] **character χ_ρ** (invariant) — trace class function; χ(1) = rank guard; ρ need not be faithful.
- [ ] **GroupModuleHomset Hom_{R[G]}(M,N)** — equivariance checked `f(g·eᵢ) = g·f(eᵢ)`. ⚠ Ranges over every g ∈ G; inconsistent with group_lattices which checks generators only (source).
- [ ] **act / action_of / action_matrix; is_invariant** (constructions/predicate) — invariance decided on group generators.
- [ ] **module_invariants M^G** — right kernel of stacked `(ρ(g) − 1)ᵀ`; row-vector convention documented (untransposed answers the dual representation).
- [ ] **module_coinvariants M_G** — `M/⟨gv − v⟩` as presented module. ⚠ Relation labels are the relation elements; coincident relations collapse (inferred). ⚠ Distinct from group_lattices "coinvariant lattice" (source).
- [ ] **_index_characters** — absolutely irreducible when split, else Gal(K/F)-orbit sums (F-irreducible).
- [ ] **_base_field_automorphisms Gal(K/F)**.
- [ ] **_isotypic_projector p_χ** — `(deg ψ/|G|) Σ χ(g⁻¹) ρ(g)`; idempotency asserted; documents that Sage's invariant.py has two cancelling errors visible off permutation actions.
- [ ] **_isotypic_component M_χ** — kernel form, automatically saturated over a PID, equivariant via centrality.
- [ ] **isotypic_decomposition ⊕ M_χ ↪ M** — carries inclusion + index; Maschke asserted as index = 1 under semisimplicity; deliberately not a coproduct. ⚠ mutation-based assembly (source).
- [ ] **_group_subobject / _restricted_action_automorphisms** — G-stable submodule with restricted action solved over Frac(R), integrality asserted.
- [ ] **hom / _equivariant_hom** — ⚠ no functoriality in G: no restriction along group homomorphisms, no induction (source).
- *(gap)* **Induction / restriction / R[G] as ring** — absent. ⚠

## `group_modules/group_lattices.sage`

- [ ] **GroupLattices(G)** (category) — integral lattices with G acting by isometries; morphisms form-preserving equivariant. ⚠ Base ring hard-wired ZZ (source). ⚠ Infinite-G premise unreachable through GroupAction (source).
- [ ] **group_lattice(L, ρ)** (construction). ⚠ Isometry axiom enforced by category-membership side channel (inferred).
- [ ] **_action_preserves_form** (axiom) — ρ lands in O(L). ⚠ Ranges over all of G (source).
- [ ] **module_representation** (forgetful) — drop form. ⚠ object-level only (source).
- [ ] **forget_action** (forgetful) — drop ρ, keep formed module. ⚠ object/element-level only (source).
- [ ] **GroupLatticeHomset** — form-preserving equivariant maps. ⚠ Routing reaches isometric homset for formless codomains (inferred). ⚠ Unbound-call delegation obscures equivariance-check route (inferred).
- [ ] **_check_equivariance** (axiom, conditional) — checked on group generators × module generators. ⚠ Default check_equivariance=False: membership is not proof of equivariance (source).
- [ ] **subobject_on / _formed_group_subobject / _equip** — G-submodule with pulled-back form.
- [ ] **invariant_lattice L^G** (distinguished) — invariant submodule re-equipped.
- [ ] **coinvariant_lattice (L^G)^⊥** (distinguished) — orthogonal complement. ⚠ Not the module coinvariants; same word, different object (source). ⚠ Nondegeneracy never asserted (inferred).
- [ ] **isotypic_lattice L_χ; isotypic_decomposition** — ⚠ decomposition returns the unformed module decomposition annotated as lattices (source).
- *(gap)* **O(L) as object, genus/discriminant interaction, induction/restriction** — absent. ⚠

### Cross-file contradictions (from inv-morphisms)

1. **Finiteness**: GroupAction asserts G finite with full value table, while GroupLattices/Homset are written on the premise of infinite-group support; only the first is enforced.
2. **"Coinvariants"**: module_coinvariants = M/⟨gv−v⟩ vs coinvariant_lattice = (L^G)^⊥; coincide only up to finite index under hypotheses stated nowhere.

## Forms and formed modules

Source files: `categories/forms/{forms,gram_matrices}.sage`, `categories/modules/framed/formed/{form_modules,lattice_axioms,lattices}.sage`, `categories/modules/framed/formed/torsionform/{torsion_modules_with_form,discriminant_bilinear_modules,discriminant_quadratic_modules}.sage`.

Value-target regime: a bilinear form is a morphism `M ⊗_R M → W` for arbitrary `W` (used: `R`, `ℚ`, `ℚ/ℤ`); a quadratic form is a morphism `Γ²M → W` (used: `ℚ/2ℤ`, `ℚ`). Bilinear and quadratic are kept genuinely distinct (sibling categories, separate homsets); the one bridge is polarization, defined only for `W = ℚ/nℤ` by halving the modulus. Exactly one morphism notion: `FormMorphism` = module map whose pullback of the codomain form equals the domain form.

### Categories

- [ ] **FormModules(R)** — modules with a form morphism; morphisms form-preserving. ⚠ sits under FramedModules, so every formed object carries a chosen generating set
- [ ] **BilinearFormModules(R)**; **SymmetricBilinearFormModules(R)** ⚠ symmetry decided as a Gram-matrix condition in the framing; **QuadraticFormModules(R)**
- [ ] **FreeFormModules(R)**; **FinitelyGeneratedFormModules(R)**; **FinitelyGeneratedFreeFormModules(R)** — where dual, correlation, radical, nondegeneracy live
- [ ] **Lattices(R)** = SymmetricBilinearFormModules(R).Projective() — projective modules with symmetric bilinear form; deliberately not f.g./integral/nondegenerate. ⚠ FormModule's lattice gate hard-wires `R = ℤ` and value module `ℤ`, contradicting the general-base claim
- [ ] **TorsionModulesWithForm(R)** — finite torsion modules with a form. ⚠ admits only `R = ℤ`
- [ ] **CokernelForms** — torsion forms presented as `coker(f)` for finite-index `f : L → M`
- [ ] **DiscriminantForms** — the refinement where `f` is the domain's own correlation, `A_L = coker(c : L → L^∨)`
- [ ] **DiscriminantBilinearModules** — finite torsion + symmetric `ℚ/ℤ`-valued `b`. ⚠ objects need not arise from a lattice despite the name
- [ ] **DiscriminantQuadraticModules** — finite torsion + `q : A → ℚ/2ℤ`; sibling, not refinement, of the bilinear category (polarization forgets)

### Axioms

- [ ] **FinitelyGenerated**; **Integral** ⚠ stated meaning (values in R) vs implementation (Gram entries integral over ℤ) differ once R ≠ ℤ; **Nondegenerate** (rad = 0, injectivity of correlation); **Projective**
- [ ] ⚠ *Absent from the formed tree*: even, odd, unimodular, definite, signature — they live only in `integrallattice/`; yet `is_even` is a hard dependency of the discriminant-quadratic cokernel

### Constructions — graded powers and classification of forms

- [ ] **TensorPower / SymmetricPower / AlternatingPower / DividedPower** `T^n, Sym^n, Λ^n, Γ^n` of a module ⚠ built by one right-exact degree construction; wrong for `Γ^n` of a non-free presented module (Γ not right exact)
- [ ] **TensorSquare** `M ⊗ M` (domain of a bilinear form); **DividedSquare** `Γ²M` (domain of a quadratic form); **γ₂(x)** the divided square element
- [ ] **divided_power_invariant_inclusion** `Γ^n M → (M^{⊗n})^{Σ_n}`; **tensor_power_polarization** `M^{⊗n} → Γ^n M`; **Σ_n action** on tensor powers
- [ ] **classifying_morphism** — the honest universal property: `q : M → W` quadratic ↔ linear `Γ²M → W` (both directions constructed)
- [ ] **BilinearFormMorphism / QuadraticFormMorphism** — forms as morphisms; Gram matrix in the chosen framing ⚠ symmetry not required at construction; quadratic case representable only via matrix, so no basis-free q ⚠ `polar_form` on bilinear forms returns the form itself (misnamed: the polar of the norm is 2b)
- [ ] **pullback f*b** (honest, contravariant); **base_changed** (transport along ring map) ⚠ value module forced to be a ring
- [ ] **polarization** `q ↦ b_q` — the halved-modulus reading `ℚ/2ℤ → ℚ/ℤ` (Nikulin's convention baked into value modules) ⚠ exists only for `ℚ/nℤ` targets
- [ ] **value submodule / scale** `𝔰(L) ⊆ W` — image of the form (O'Meara's scale when W = R)
- [ ] **descends_along** predicate ⚠ integrality hard-coded to ℤ

### Constructions — formed-module structure

- [ ] **forget_form** ⚠ object-level only, not a functor
- [ ] **gram_tensor** — the form as a type-(0,2) tensor; **raise/lower index** ⚠ raising needs unimodularity, ungated; **raise_index_over_fraction_field**
- [ ] **dual_module** `Hom(L,R)`; **correlation_morphism** `c : L → L^∨` (honest morphism, matrix G); **correlation_of** into the dual *lattice* (Gram G⁻¹)
- [ ] **radical** `rad(L) = ker c` as genuine kernel subobject; **is_nondegenerate** = injectivity of c
- [ ] **subobject_on** — sublattice generated by elements with induced Gram ⚠ `_sub_form_module` always builds a *bilinear* form: a subobject of a quadratic module loses q
- [ ] **FormHomset / FormMorphism** — with kernel, cokernel, image, index, orthogonal complement, composition ⚠ value-module mismatch silently reduced before comparison
- [ ] **FormAutomorphismGroup** `O(L)` — form-preserving automorphisms of unit determinant
- [ ] **isotropic_reduction** of an element's span

### Constructions — torsion forms and discriminants

- [ ] **from_module / from_relations_and_gram** — torsion (bi)linear/quadratic forms from presentation + Gram, descent conditions asserted (b integral on relations; q even on relations)
- [ ] **cokernel** functor-shaped: `coker(f)` carrying codomain Gram ⚠ justification valid for `f = c`, but arbitrary finite-index f accepted; quadratic case gated on `is_even` of the domain
- [ ] **invariants / cardinality / annihilator / primary_part / primary_decomposition / is_p_elementary** of the underlying finite group
- [ ] **isotropic_subobjects / maximal_isotropic_subobjects** — enumerated by closure
- [ ] **p_adic_jordan_module_generators** — p-adic Jordan normal form of a torsion form (Peters–Sterk 11.2.3) ⚠ Gram-matrix-first, representative-dependent engine matrix
- [ ] **normal_form** (bilinear and quadratic) — unique for odd p; at p = 2 only the quadratic side has uniqueness (Peters–Sterk C.3.2); Gauss-sum invariants have no bilinear analogue
- [ ] **associated_quadratic_form** ⚠ docstring requires evenness of the source lattice; code never consults it
- [ ] **associated_bilinear_form** (honest) — polarization to the sibling category
- [ ] **invariant_factor_form** — form on invariant-factor generators (merges summands; not the discriminant group itself)
- [ ] **regenerating_data / regenerate / relations_among** — rewriting a torsion form on a new generating set ⚠ quadratic round-trip goes through the polarization lift, delicate at p = 2
- [ ] **is_characteristic** (element) — the Wu/characteristic element condition `q(x) ≡ b(x,v) mod ℤ`
- [ ] **form_vanishes_on** — pairwise vanishing (bilinear) vs valuewise vanishing (quadratic, strictly stronger)

### Defects to fix in formalization (forms)

- ⚠ FormModules under FramedModules: every notion (symmetry, integrality, scale, radical, discriminant Gram, block decomposition) computed from a Gram matrix in a chosen framing while docstrings claim the basis-free reading; only `radical`, `correlation_morphism`, `_value_submodule` honor it
- ⚠ `_matrix_connected_component_cuts` (gram_matrices.sage): orthogonal decomposition is framing-dependent and misses non-consecutive blocks
- ⚠ `Lattices.__classcall_private__` is category and object constructor in one callable
- ⚠ QuadraticFormMorphism's `gram_matrix` and stored symmetric lift: two matrices name one object; `lift_form` value module hard-coded to ℚ
- ⚠ Unframed bilinear branch is a bare set map with bilinearity trusted; unframed quadratic forms cannot be stated at all

## Integral lattices, root systems, Coxeter diagrams

Source files: `categories/modules/framed/formed/integrallattice/{integral_lattices,lattice_homomorphisms,lattice_isometries,subobjects,root_lattices,definite_lattices,hyperbolic_lattices,coxeter_diagrams}.sage`.

Named lattices in this tree: only `U`/`H` and the ADE root lattices from Cartan matrices; `E8`, `K3`, Enriques, Sterk-specific lattices live in `catalogue.sage`. Vinberg is delegated to a vendored `vinal`; no elliptic/parabolic/Lannér subdiagram classification exists.

### Categories and axioms

- [ ] **FinitelyGeneratedIntegralLattices** — the `Integral` axiom on f.g. lattices
- [ ] **IntegralLattices** — f.g., integral-valued, nondegenerate lattices over a base defaulting to ℤ ⚠ name says integral but silently asserts nondegeneracy, while degenerate integral lattices are deliberately constructed elsewhere
- [ ] **Nondegenerate** (axiom) — correlation injective
- [ ] **LatticeHomomorphisms** — form-preserving module maps ⚠ nothing separates isometric embeddings (injective, primitive) from arbitrary form-preserving maps
- [ ] **LatticeIsometries** — `O(L)` and subgroups as endomorphism homsets ⚠ admission by unit determinant; never connected to `is_isometric`
- [ ] **Subobjects** — module + chosen monomorphism `ι : S ↪ B`; object of the ambient category, never a subset
- [ ] **RootLattices** — lattices presented by a Cartan matrix; both signs are members ⚠ the root-system datum is asserted at refinement, never verified against the Gram matrix
- [ ] **RootLatticeIsometries**; **DefiniteLattices** (either sign) ⚠ no certifying predicate at admission; **DefiniteLattices.Subobjects** (where LLL reduction lives)
- [ ] **HyperbolicLattices** — signature (n,1) ⚠ three sign conventions in one category: docstring (n,1), refine admits min(p,q)=1, Vinberg twists (1,n)
- [ ] **CoxeterDiagrams** — finite Coxeter diagrams; morphisms preserve every exponent m_ij

### Predicates and invariants

- [ ] **is_unimodular** (c iso); **is_even** (q ∈ 2ℤ on generators); **is_coeven/is_coodd + delta** (Nikulin δ) ⚠ stated for all lattices though δ is 2-elementary; **is_p_elementary**
- [ ] **is_elliptic** (neg. definite); **is_parabolic** (neg. semidefinite) ⚠ overlaps elliptic; usual meaning requires nonzero radical
- [ ] **is_decomposable / decomposition / summands** ⚠ framing-dependent block detection, not the isometry-invariant notion; permutation-requiring splittings refused
- [ ] **is_isometric** ⚠ fuses three claims: genus equality implies isometry only for indefinite rank ≥ 3 outside spinor-exceptional genera (Eichler); binary branch rejects odd rank-2; definite branch feeds `QuadraticForm(±G)` undoubled while lattice_isometries doubles to 2G
- [ ] **q(x), b(x,y)** ⚠ q is the bilinear self-pairing (not ½⟨x,x⟩); discriminant q valued in ℚ/2ℤ consistently
- [ ] **div(x)** — divisibility of a vector; **gram_of**; **signature_pair** (Sylvester, defined for degenerate L too)
- [ ] **discriminant** — the *signed* determinant `(−1)^{n(n−1)/2} det G` ⚠ diverges from the common `det G` convention; `_latex_` displays det G, so one word denotes two numbers
- [ ] **genus** — Conway–Sloane genus symbol; **minimum**; **enumerate_short_vectors** (positive definite only)
- [ ] **is_primitive** (element) — torsion-free cokernel of `ℤv ↪ L`, deliberately not gcd of coordinates
- [ ] **get_isotropic_type** — cusp type of a primitive isotropic vector (Odd / Even characteristic / Even ordinary) ⚠ presumes 2-elementary, unchecked

### Constructions

- [ ] **dual_lattice** `L^∨` (Gram G⁻¹ on the same framing set; explicitly not the subset of L ⊗ ℚ) ⚠ object-level, no morphism action
- [ ] **correlation / dual_embedding** `c : L → L^∨`; **correlation_isomorphism** (unimodular case); **dual_basis**
- [ ] **discriminant_bilinear_form** `(A_L, b)` in ℚ/ℤ; **discriminant_quadratic_form** `(A_L, q)` in ℚ/2ℤ (gated on evenness, correct obstruction); **discriminant_group** (with p-primary option)
- [ ] **discriminant_projection** `π : L^∨ → A_L`; **divided_discriminant_class** `e/div(e) ∈ A_L`
- [ ] **glue(classes)** — overlattice from discriminant classes ⚠ isotropy of inputs is a real hypothesis, never asserted
- [ ] **maximal_overlattice** — from a maximal isotropic subgroup of A_L (Nikulin 1.4.1); *a* maximal overlattice, not *the*
- [ ] **I_perp_mod_I / e_perp_mod_e** — `I^⊥/I` for isotropic subobjects
- [ ] **direct_sum / ⊕ / powers** — block-diagonal Gram ⚠ object-level, biproduct in name only
- [ ] **twist** `L(n)`; **tensor** `L ⊗ M` (Kronecker Gram; the one operation carrying an explicit structure morphism)
- [ ] **Hom / End / Aut = O(L)** — O(L) as units of End(L) ⚠ finite presentation for indefinite L attributed to Borel–Harish-Chandra, which gives finite generation; finite presentation is Borel–Serre/Raghunathan
- [ ] **with_action(ρ)**; **invariant_lattice** `L^G` (trivial isotypic component, not ker(g−1)); **coinvariant_lattice** `(L^G)^⊥` ⚠ "coinvariants" = orthogonal complement here, ≠ the quotient L_G; agree only up to finite index
- [ ] **subobject machinery** — is_primitive/is_saturated (`M/S` torsion-free — the repo-wide definition), **saturation** (primitive closure via torsion of the quotient), **index**, **index_in_saturation**
- [ ] **isotropic_reduction** `S^⊥/S` for totally isotropic S ⚠ primitivity not required; non-saturated S gives a torsion quotient whose "Gram" is not a form on a free module
- [ ] **named lattices** `U`/`H`; ADE root lattices from Cartan matrices ⚠ sign drift: names build positive definite (+2 diagonal) while the catalogue twists to negative definite; both circulate under one name
- [ ] **register_indecomposable** — summand naming ⚠ by literal Gram equality in a chosen framing, not isometry
- [ ] **refine_root_lattice / cartan_type** — records the root system; **O(L) = W(R) ⋊ Γ(R)** order formula (simply laced only; F₄ counterexample recorded)
- [ ] **LLL** (definite subobjects) — reduced framing of the same subobject; requires ambient Gram literally ±identity
- [ ] **vinberg_algorithm** — root enumeration for hyperbolic reflection groups (vendored vinal + CoxIter covolume check) ⚠ non-termination downgraded to a warning: returned roots not certified as simple roots of a fundamental polyhedron
- [ ] **isometry group machinery** — Plesken–Souvignier generators for definite O(L) (via ±2G), GAP-backed order/enumeration/presentation, `subgroup_on`, `cyclic_subgroup` ⚠ `is_countable` returns False for infinite O(L), which is wrong (always countable)

### Coxeter diagrams

- [ ] **minimal_edge_lattices** — the five rank-2 realizations for norms −2/−4: orthogonal (m=2), single (m=3), double (m=4), parallel (m=∞ degenerate), ultraparallel (m=∞ indefinite); crystallographic restriction tightened to m ∈ {2,3,4} ⚠ contradicted by the file's own m=6 triple-edge drawing convention
- [ ] **_coxeter_exponent** — bond m from `(2cos θ)² = 4b²/(q·q)` (Vinberg) ⚠ non-crystallographic angles abort rather than being represented
- [ ] **from_coxeter_matrix / from_cartan_type / from_roots** — diagram from matrix, type, or a root family in an ambient lattice ⚠ from_roots: linear independence unchecked, so the abstract root lattice need not embed; primitivity of the root span never considered
- [ ] **FiniteCoxeterDiagram** — optionally *rooted*: carries actual roots, root_morphism, root_lattice (abstract), root_realization (ambient), root_intersection_matrix/graph (with self-loop root squares)
- [ ] **subdiagram** (induced); **Aut** (edge-label-preserving graph automorphisms) ⚠ annotated as ModuleAutomorphismGroup but returns a permutation group, in no owned category
- [ ] **root-square node convention** — white = −4, black = −2 ⚠ pins the setting to 2-elementary hyperbolic; other squares abort
- [ ] **CoxeterDiagramHomset/Morphism** — exponent-preserving vertex maps with composition

### Defects to fix in formalization (lattices)

- ⚠ No functor anywhere: `L ↦ L^∨`, `L ↦ A_L`, `L ↦ L(n)`, ⊕, ⊗, `L ↦ O(L)`, `L ↦ L^G` all lack morphism actions (only ⊗ carries a structure morphism)
- ⚠ Isometry vs isomorphism conflated: unit-determinant admission, genus-based `is_isometric`, and the isometry homset are never connected
- ⚠ No single sign convention: Cartan names positive definite, catalogue negative; elliptic/parabolic on negated Gram; Vinberg twists; Coxeter colors assume −2/−4
- ⚠ Gram-matrix-relative where basis-free intended: decomposability, summand naming, block cuts, LLL precondition

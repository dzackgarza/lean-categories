/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Sublattice
public import LeanCategories.Lattices.Valued.ChangeValue
public import LeanCategories.Lattices.Valued.Standard
public import LeanCategories.ForMathlib.CosliceGroupoid
public import LeanCategories.ForMathlib.LinearMapCompl
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Action.Basic

/-!
# Arrow-category loci, markings as coslice objects, and the `BC₂` involution

Three constructions about `W`-valued `R`-lattices `Lat_R`, in the arrow-category modelling of
`FOUNDATIONS.md` §27–§28 (tracked by issue #27, split from `research#13`).

## 1. Primitive-embedding loci

`FOUNDATIONS.md` Definition 28.1 fixes the convention: an isometric embedding `i : L ↪ M` is
primitive when its cokernel is torsion-free, and "primitive embeddings form a locus in the arrow
category `Ar(Lat_R)`". The source is Nikulin 1980, §§1°, 5°–6°: `§5°` of the text
(`.tmp-sources/nikulin-1980-integral-symmetric-bilinear-forms.md`, line 232) distinguishes two
equivalence relations on primitive embeddings, and the first is the arrow-category one:

> Two primitive embeddings `S ⊂ M` and `S ↪ M′` will be called isomorphic if there exists an
> isomorphism between `M` and `M′` reducing to the identity map on `S`. If there exists an
> isomorphism between `M` and `M′` taking `S` into itself, we shall regard `S ↪ M` and
> `S ↪ M′` as defining isomorphic primitive sublattices.

The distinction is exactly why the embedding, not the submodule, must be the object: the second
relation quotients by `O(M)`, the first does not. `primitiveEmbeddingLocus` is the first, and
`primitiveEmbeddingLocus_of_arrow_isoMk` says it is a locus of the arrow category rather than a
predicate on pairs of lattices.

*Named-section status of the locus itself: no named section is needed.* The locus is a `Prop`-valued
object property of arrows, so its classifying fiber over a fixed arrow is empty or contractible
(`primitiveEmbeddingLocus_fibre_subsingleton`); an object of the locus *is* its arrow.

The residual choice is the **primitive completion**. `§5°`, line 234 of the same source:
"Let `S ↪ M` be a primitive embedding, and let `K = (S)^⊥_M`. Then `S ⊕ K ⊂ M`, and `M` is an
overlattice of `S ⊕ K`." The complement `K` is forced, but `S ⊕ K` is only *contained* in `M` with
torsion cokernel, and a completion that splits the embedding is additional data:
`PrimitiveCompletion` below, whose fiber is *not* a subsingleton
(`exists_distinct_primitiveCompletions`, over the standard rank-two lattice with `S = ⟨e₀⟩`).
A consumer of a primitive embedding that needs a completion names its section; `Nonempty` is not
enough.

## 2. Markings as coslice objects

`FOUNDATIONS.md` Definition 28.3: for a fixed reference lattice `Λ`, a marking of `L` is an isometry
`η : Λ ≅ L`, and marked lattices form the coslice (or comma) category over the *core* of lattices.
`MarkedLatticeCat` is `Under ⟨Λ⟩` in `Core (Lat_R)`, i.e. `Λ ↓ Lat_R^≃`. The definition of a marking
and of an isomorphism of marked objects is Alexeev–Engel, *Compact moduli of K3 surfaces*
(arXiv 2101.12186v2, `.tmp-sources/ae-2101.12186v2.md`): Definition 2.6 fixes the reference lattice,
Definition 2.7 (line 156) defines a marking as an isometry `σ : H²(X,ℤ) → L_K3` (here `Λ → L` in the
convention of Definition 28.3), and Definition 2.8 (line 158) defines an isomorphism of marked
objects as an isomorphism `f` with `σ ∘ f* = σ'`. `markingHom_marking_comp` is Definition 2.8 in
this category's terms.

*Named-section status: noncontractible, a named section is mandatory.* The fiber of the marking
projection over a fixed `L` is the set of isometries `Λ ≅ L`, which is a torsor under `Aut Λ`
(`existsUnique_marking_factor`; Alexeev–Engel line 286 calls `Γ = {γ ∈ O(L_K3) : γ|_M = id_M}` "the
group of changes-of-marking", and line 729 states the torsor statement for the induced markings).
It is a subsingleton exactly when `Aut Λ` is trivial (`markingFibre_subsingleton_iff`), and `−id` is
a second marking of any torsion-free integral lattice with a nonzero vector
(`negIso_ne_refl`). Every consumer of a marked object names its marking, which is the object's own
arrow `X.hom`; `marking` exposes it.

The coslice universal property is the one the issue asks for: the marked lattice `(Λ, id_Λ)` is the
*initial* object of `Λ ↓ Lat_R^≃` (`marking_initial`, Mathlib's `Under.mkIdInitial`), so every
marked lattice receives exactly one morphism from it; and because the base is a groupoid, any two
morphisms of markings with the same source and target coincide (`markingHom_subsingleton`). The
coslice is therefore *contractible as a category*, which is precisely why contractibility of the
total space cannot be the criterion: the information is in the object and in the fiber over a
fixed codomain.

## 3. `BC₂` involution actions, and the `(−1)` change-of-value functor

`FOUNDATIONS.md` Definition 28.4: for a group `G`, a `G`-action on a lattice is a functor
`BG → Lat_R^≃`, and an involution is the case `G = C₂`, equivalently an isometry `σ` with `σ² = 1`.
`BC2` is the group `C₂` and `BC2Action` is Mathlib's `Action (Core Lat_R) BC2`, which is by
construction a functor out of the one-object groupoid `BC₂` into the core, so the generator of `C₂`
acts by an automorphism of the lattice; `BC2Action.gen_sq` derives `σ² = 1` from the functor laws
and from `2 = 0` in `C₂`, giving Definition 28.4's equivalent reading on the functorial side.

The anti-isometry mechanism is the **`(−1)` change-of-value-module functor**, not a sign convention:
`negValueChange` is `changeValue` (`Lattices/Valued/ChangeValue.lean`, homed in
lean-categories#101) along `−1 : W → W`, it is an involution of `Lat_R` up to definitional equality
(`negValueChange_comp_self`), and `isometry_neg_iff` identifies an anti-isometry `φ` with an
*isometry* `φ : L₁ → (−1)·L₂`. Nikulin 1980 §4° (via `FOUNDATIONS.md` Definition 27.5) states the
anti-isometry condition as `q₂(φx) = −q₁(x)`; Prop. 1.5.1 (line 248 of the same extraction) applies
it as `q_K ∘ γ = −q_S|H`. `antiIsometry_comp` records the consequence that makes the mechanism worth
naming: two anti-isometries compose to an isometry, which is exactly the statement that the twist is
an involution.

## Provenance and searches

* Mathlib (pinned revision, searched in `Mathlib/`): `CategoryTheory.Arrow` and `Comma`
  (`CategoryTheory/Comma/Basic.lean`, `CategoryTheory/Comma/Arrow.lean`), `Under`
  (`CategoryTheory/Comma/Over/Basic.lean:664`, with `Under.w` and `Under.mkIdInitial`), `Core`
  (`CategoryTheory/Core.lean`, `Core.isoMk`), `Action`
  (`CategoryTheory/Action/Basic.lean:44`), `ObjectProperty.isoMk`
  (`CategoryTheory/ObjectProperty/FullSubcategory.lean:102`), `LinearMap.ker`/`range` and
  `Submodule.disjoint_def`. The commutation of the arrow category is `Arrow.isoMk`. Mathlib has no
  component-extraction lemma for a `Comma`-isomorphism (no `Comma.isIso_left`) and no thinness
  statement for `Under` over a groupoid, which is why `ForMathlib/CosliceGroupoid.lean` supplies the
  latter.
* This repository: `BilinModuleCat.IsPrimitiveEmbedding`, `IsPrimitiveSubmodule` and
  `IsPrimitiveSubmodule.map_equiv_iff` (`Lattices/Valued/Sublattice.lean:24`, `:61`, `:173`),
  `orthogonalComplement` (`:328`), `changeValue` and `changeValue_id`/`changeValue_comp`
  (`Lattices/Valued/ChangeValue.lean`, `Modules/Bilinear/Valued/ChangeValue.lean`),
  `LatticeAutomorphismGroup`/`latticeAutEquivOrthogonalGroup`
  (`Lattices/Valued/OrthogonalGroup.lean:25`), `Involution` (`Lattices/Valued/Involution.lean`),
  `rankOneLattice`/`latticeOfGramMatrix` (`Lattices/Valued/Standard.lean:75`, `:140`),
  `EquivariantLatticeCat` and its invariant/coinvariant lattices
  (`Lattices/Valued/Equivariant.lean:39`, `:61`, `:65`) for Definition 28.5.
  Queries run (repository and Mathlib): `primitive embedding locus arrow category`,
  `IsPrimitiveEmbedding`, `primitive completion`, `saturation primitive submodule`,
  `marking isometry reference lattice`, `Under core coslice`, `coslice groupoid unique morphism`,
  `StructuredArrow subsingleton`, `BC2 involution action lattice`, `changeValue neg`,
  `anti-isometry discriminant`, `LinearMap IsCompl ker range`, `isCompl leftInverse`,
  `torsor markings isometry group`.
* Sources in `.tmp-sources/`: `nikulin-1980-integral-symmetric-bilinear-forms.md` (lines 232, 234,
  248, 270) and `ae-2101.12186v2.md` (lines 152, 156, 158, 282, 286, 290, 729).
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable (R : Type u) [CommRing R] (W : Type u) [AddCommGroup W] [Module R W]

/-! ## 1. Primitive-embedding loci in the arrow category -/

/-- The locus of primitive embeddings in the arrow category of `Lat_R`: an object of the arrow
category is an arrow `S ⟶ M`, and it lies in the locus when it is a primitive formed embedding.

The embedding is the object, per `FOUNDATIONS.md` Definition 28.1 and Nikulin 1980 §5° (line 232 of
`.tmp-sources/nikulin-1980-integral-symmetric-bilinear-forms.md`), whose first — arrow-category —
notion of isomorphism of primitive embeddings is what this locus's morphisms realize. -/
def primitiveEmbeddingLocus : ObjectProperty (Arrow (LatticeCat R W)) :=
  fun f => BilinModuleCat.IsPrimitiveEmbedding f.hom.hom

/-- The locus as a category: objects are primitive embeddings, morphisms are the commutative squares
of the arrow category. -/
abbrev PrimitiveEmbeddingArrowCat := (primitiveEmbeddingLocus R W).FullSubcategory

/-- The classifying fiber of the primitive-embedding locus over a fixed arrow is a subsingleton:
the locus is `Prop`-valued, so an arrow either is a primitive embedding or is not, uniquely. No
named section is needed for it. -/
theorem primitiveEmbeddingLocus_fibre_subsingleton
    (X Y : PrimitiveEmbeddingArrowCat R W) (h : X.obj = Y.obj) : X = Y :=
  ObjectProperty.FullSubcategory.ext h

/-- Primitivity of a formed embedding is a property of the arrow up to isomorphism of its two ends:
if `g` is `f` conjugated by isomorphisms of source and target, then `g` is primitive whenever `f`
is. -/
theorem BilinModuleCat.IsPrimitiveEmbedding.of_iso {L₁ M₁ L₂ M₂ : BilinModuleCat R W}
    (f : L₁ ⟶ M₁) (g : L₂ ⟶ M₂) (eL : L₁ ≅ L₂) (eM : M₁ ≅ M₂)
    (hsq : eL.hom ≫ g = f ≫ eM.hom)
    (hf : BilinModuleCat.IsPrimitiveEmbedding f) :
    BilinModuleCat.IsPrimitiveEmbedding g := by
  have hsq' : (BilinModuleCat.underlyingMap g).comp (BilinModuleCat.underlyingMap eL.hom) =
      (BilinModuleCat.underlyingMap eM.hom).comp
        (BilinModuleCat.underlyingMap f) := by
    have h := congrArg BilinModuleCat.underlyingMap hsq
    simpa using h
  have hkey : ∀ x : L₁.carrier,
      BilinModuleCat.underlyingMap g (BilinModuleCat.underlyingMap eL.hom x) =
        BilinModuleCat.underlyingMap eM.hom (BilinModuleCat.underlyingMap f x) :=
    fun x => LinearMap.congr_fun hsq' x
  have hkeyL : ∀ x : L₁.carrier,
      BilinModuleCat.underlyingMap g (BilinModuleCat.linearEquivOfIso eL x) =
        BilinModuleCat.linearEquivOfIso eM (BilinModuleCat.underlyingMap f x) := by
    intro x
    simpa using hkey x
  have hinj : Function.Injective (BilinModuleCat.underlyingMap g) := by
    intro a b hab
    obtain ⟨a', rfl⟩ := (BilinModuleCat.linearEquivOfIso eL).surjective a
    obtain ⟨b', rfl⟩ := (BilinModuleCat.linearEquivOfIso eL).surjective b
    rw [hkeyL a', hkeyL b'] at hab
    have h0 := (BilinModuleCat.linearEquivOfIso eM).injective hab
    rw [hf.1 h0]
  refine ⟨hinj, ?_⟩
  have hrange : LinearMap.range (BilinModuleCat.underlyingMap g) =
      (LinearMap.range (BilinModuleCat.underlyingMap f)).map
        (BilinModuleCat.linearEquivOfIso eM : M₁.carrier →ₗ[R] M₂.carrier) := by
    refine SetLike.ext fun z => ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := (BilinModuleCat.linearEquivOfIso eL).surjective y
      refine Submodule.mem_map.mpr ⟨_, ⟨x, rfl⟩, ?_⟩
      exact (hkeyL x).symm
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨BilinModuleCat.linearEquivOfIso eL x, hkeyL x⟩
  rw [hrange]
  exact (IsPrimitiveSubmodule.map_equiv_iff (BilinModuleCat.linearEquivOfIso eM) _).mpr hf.2

/-- The primitive-embedding locus is a locus of the arrow category: two arrows that are isomorphic
as objects of `Arrow (Lat_R)` — presented, as `Arrow.isoMk` presents them, by isomorphisms of the
two ends together with the commutation square — are simultaneously primitive. -/
theorem primitiveEmbeddingLocus_of_arrow_isoMk {f g : Arrow (LatticeCat R W)}
    (l : f.left ≅ g.left) (r : f.right ≅ g.right)
    (h : l.hom ≫ g.hom = f.hom ≫ r.hom)
    (hf : primitiveEmbeddingLocus R W f) : primitiveEmbeddingLocus R W g :=
  BilinModuleCat.IsPrimitiveEmbedding.of_iso (R := R) (W := W)
    f.hom.hom g.hom.hom ((isLattice R W).ι.mapIso l) ((isLattice R W).ι.mapIso r)
    (by simpa using congrArg (fun k => k.hom) h) hf

/-! ### The residual choice: primitive completions -/

/-- A primitive completion of an arrow `f : S ⟶ M`: a complement of the image of `f` inside `M`.

Nikulin 1980 §5° (line 234) forces the *orthogonal* complement `K = (S)^⊥_M` and says only that
`S ⊕ K ⊂ M` with `M` an overlattice of `S ⊕ K`; a completion that splits the embedding is extra
data. The fiber of completions over one arrow is not a subsingleton
(`exists_distinct_primitiveCompletions`), so a consumer that needs one names its section rather than
asking for `Nonempty`. -/
structure PrimitiveCompletion {R : Type u} [CommRing R] {W : Type u} [AddCommGroup W]
    [Module R W] {S M : BilinModuleCat R W} (f : S ⟶ M) where
  /-- The complement of the image of the embedding. -/
  carrier : Submodule R M.carrier
  /-- The image and the complement are complementary. -/
  isCompl : IsCompl (LinearMap.range (BilinModuleCat.underlyingMap f)) carrier

namespace PrimitiveCompletion

variable {R W}

/-- A retraction of an embedding yields a primitive completion: the kernel of the retraction. -/
def ofRetraction {S M : BilinModuleCat R W} (f : S ⟶ M)
    (p : M.carrier →ₗ[R] S.carrier)
    (hp : p.comp (BilinModuleCat.underlyingMap f) = LinearMap.id) : PrimitiveCompletion f :=
  ⟨LinearMap.ker p, LinearMap.isCompl_range_ker_of_comp_eq_id _ _ hp⟩

end PrimitiveCompletion

/-! ## 2. Markings as coslice objects -/

/-- The core of the lattice category: the base of the coslice of markings, `FOUNDATIONS.md`
Definition 28.3 as amended by the foundations audit ("markings form the coslice/comma category over
the core `Lat_R^≃`"). -/
abbrev LatticeCore := Core (LatticeCat R W)

/-- Marked lattices by the reference lattice `Λ`: the coslice `Λ ↓ Lat_R^≃`. An object is a pair of
a lattice and an isometry `Λ ≅ L`; a morphism is an isometry of lattices commuting with the
markings. -/
abbrev MarkedLatticeCat (Λ : LatticeCat R W) := Under (⟨Λ⟩ : LatticeCore R W)

namespace MarkedLatticeCat

variable {R W} {Λ : LatticeCat R W}

/-- The underlying lattice of a marked lattice. -/
def underlying (X : MarkedLatticeCat R W Λ) : LatticeCat R W := X.right.of

/-- The marking carried by a marked lattice — the named section of the marked object, as data. -/
def marking (X : MarkedLatticeCat R W Λ) : Λ ≅ X.underlying := X.hom.iso

/-- A morphism of markings is an isometry of the underlying lattices commuting with the two markings
(`FOUNDATIONS.md` Definition 28.3; Alexeev–Engel, arXiv 2101.12186v2, Definition 2.8, line 158). -/
theorem markingHom_marking_comp {X Y : MarkedLatticeCat R W Λ} (φ : X ⟶ Y) :
    X.marking ≪≫ φ.right.iso = Y.marking := by
  have h : X.hom ≫ φ.right = Y.hom := Under.w φ
  change X.hom.iso ≪≫ φ.right.iso = Y.hom.iso
  rw [← CategoryTheory.coreCategory_comp_iso, h]

/-- Two morphisms of markings with the same source and target agree: the coslice over the core is a
thin category, so "being a morphism of markings" is a proposition. -/
theorem markingHom_subsingleton (X Y : MarkedLatticeCat R W Λ) : Subsingleton (X ⟶ Y) :=
  Under.subsingleton_hom X Y

/-- The coslice universal property: the marked lattice `(Λ, id_Λ)` is initial in `Λ ↓ Lat_R^≃`. -/
def markingInitial (Λ : LatticeCat R W) :
    IsInitial (Under.mk (𝟙 (⟨Λ⟩ : LatticeCore R W))) :=
  Under.mkIdInitial

/-- The fibre of the marking projection over a fixed lattice: the markings of `L` by `Λ`, i.e. the
isometries `Λ ≅ L`. -/
abbrev markingFibre (Λ L : LatticeCat R W) := Λ ≅ L

/-- The markings of a fixed lattice form a torsor under the isometry group of the reference lattice:
for any two markings of `L` there is a unique isometry `g` of `Λ` carrying one to the other. This is
the torsor structure that makes the marking fiber noncontractible (Alexeev–Engel, arXiv
2101.12186v2, line 286, "the group of changes-of-marking"; the torsor statement is line 729). -/
theorem existsUnique_marking_factor {L : LatticeCat R W} (η η' : markingFibre Λ L) :
    ∃! g : Λ ≅ Λ, g ≪≫ η' = η := by
  refine ⟨Iso.trans η η'.symm, ?_, ?_⟩
  · apply Iso.ext
    simp
  · intro g hg
    apply Iso.ext
    have h2 := congrArg (fun k => k.hom) hg
    simp only [Iso.trans_hom] at h2
    calc g.hom = (g.hom ≫ η'.hom) ≫ η'.inv := by simp
      _ = η.hom ≫ η'.inv := by rw [h2]

end MarkedLatticeCat

/-! ### The concrete witnesses for the two classifications -/

section Witnesses

/-- The Gram matrix of the standard positive-definite rank-two lattice. -/
def standardTwoGramMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 1]

/-- The standard positive-definite rank-two lattice over `ℤ`. -/
def standardTwoLattice : IntegralLatticeCat ℤ :=
  latticeOfGramMatrix standardTwoGramMatrix (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [standardTwoGramMatrix])

/-- The pairing of the standard rank-two lattice is the dot product. -/
theorem standardTwoLattice_pairing (x y : Fin 2 → ℤ) :
    standardTwoLattice.obj.pairing x y = x 0 * y 0 + x 1 * y 1 := by
  simp [standardTwoLattice, latticeOfGramMatrix, Matrix.toBilin'_apply', Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, standardTwoGramMatrix]

/-- The inclusion of the first coordinate, `ℤ → ℤ²`. -/
def coordInclusion : (Fin 1 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := fun j => if j = 0 then x 0 else 0
  map_add' := by intro x y; funext j; fin_cases j <;> simp
  map_smul' := by intro c x; funext j; fin_cases j <;> simp

/-- The projection onto the first coordinate, a retraction of `coordInclusion`. -/
def coordZero : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 1 → ℤ) where
  toFun v := fun _ => v 0
  map_add' := by intro x y; funext k; fin_cases k; simp
  map_smul' := by intro c x; funext k; fin_cases k; simp

/-- The sum of the two coordinates, a second retraction of `coordInclusion`. -/
def coordSum : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 1 → ℤ) where
  toFun v := fun _ => v 0 + v 1
  map_add' := by intro x y; funext k; fin_cases k; simp; ring
  map_smul' := by intro c x; funext k; fin_cases k; simp; ring

theorem coordZero_comp : coordZero.comp coordInclusion = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext k
  fin_cases k
  simp [coordZero, coordInclusion]

theorem coordSum_comp : coordSum.comp coordInclusion = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext k
  fin_cases k
  simp [coordSum, coordInclusion]

/-- The embedding `⟨e₀⟩ ↪ ℤ²` of the first coordinate as a morphism of lattices. -/
def coordEmbedding : (rankOneLattice 1).obj ⟶ standardTwoLattice.obj :=
  BilinModuleCat.homMk coordInclusion (by
    intro x y
    change standardTwoLattice.obj.pairing (coordInclusion (show Fin 1 → ℤ from x))
        (coordInclusion (show Fin 1 → ℤ from y))
      = (rankOneLattice 1).obj.pairing (show Fin 1 → ℤ from x) (show Fin 1 → ℤ from y)
    rw [standardTwoLattice_pairing, rankOneLattice_pairing]
    simp [coordInclusion])

/-- `coordZero` read at the carriers of the two lattices. -/
def coordZeroCarrier :
    standardTwoLattice.obj.carrier →ₗ[ℤ] (rankOneLattice 1).obj.carrier :=
  coordZero

/-- `coordSum` read at the carriers of the two lattices. -/
def coordSumCarrier :
    standardTwoLattice.obj.carrier →ₗ[ℤ] (rankOneLattice 1).obj.carrier :=
  coordSum

/-- The complement of the embedding of the first coordinate computed from the projection onto the
first coordinate: it is `⟨e₁⟩`. -/
def completionZero : PrimitiveCompletion coordEmbedding :=
  PrimitiveCompletion.ofRetraction coordEmbedding coordZeroCarrier (by
    change coordZero.comp coordInclusion = LinearMap.id
    exact coordZero_comp)

/-- A second, distinct, complement of the same embedding, from `v ↦ v₀ + v₁`: it is
`⟨e₀ − e₁⟩`. -/
def completionSum : PrimitiveCompletion coordEmbedding :=
  PrimitiveCompletion.ofRetraction coordEmbedding coordSumCarrier (by
    change coordSum.comp coordInclusion = LinearMap.id
    exact coordSum_comp)

/-- **The primitive completion of a fixed primitive embedding is not unique.** The two retractions
`v ↦ v₀` and `v ↦ v₀ + v₁` of `⟨e₀⟩ ↪ ℤ²` give the complements `⟨e₁⟩` and `⟨e₀ − e₁⟩`. The
classifying fiber of primitive completions over one arrow is therefore not a subsingleton, and a
consumer that needs one names its section: Nikulin 1980 §5° (line 234) forces only `S ⊕ S^⊥ ⊂ M`. -/
theorem exists_distinct_primitiveCompletions :
    ∃ C₁ C₂ : PrimitiveCompletion coordEmbedding, C₁ ≠ C₂ := by
  refine ⟨completionZero, completionSum, ?_⟩
  intro h
  have hk : LinearMap.ker coordZero = LinearMap.ker coordSum :=
    congrArg PrimitiveCompletion.carrier h
  have hmem : (fun j : Fin 2 => if j = 0 then (1 : ℤ) else -1) ∈
      LinearMap.ker coordSum := by
    rw [LinearMap.mem_ker]
    funext k
    fin_cases k
    simp [coordSum]
  rw [← hk, LinearMap.mem_ker] at hmem
  have h0 := congrFun hmem 0
  simp [coordZero] at h0

/-- Negation preserves any symmetric pairing: `b(−x,−y) = b(x,y)`. -/
theorem BilinModuleCat.pairing_neg_neg (L : BilinModuleCat R W) (x y : L.carrier) :
    L.pairing (-x) (-y) = L.pairing x y := by
  have h : (-x) ⊗ₜ[R] (-y) = x ⊗ₜ[R] y := by
    rw [TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_neg]
  rw [BilinModuleCat.pairing, BilinModuleCat.pairing, h]

/-- Negation is an isometry of every `W`-valued lattice. -/
def negIso (L : LatticeCat R W) : L ≅ L :=
  (isLattice R W).isoMk (BilinModuleCat.isoMk (LinearEquiv.neg R) (by
    intro x y
    exact BilinModuleCat.pairing_neg_neg (R := R) (W := W) L.obj x y))

/-- Negation is an isometry of the rank-one standard lattice. -/
def rankOneNegIso : rankOneLattice 1 ≅ rankOneLattice 1 :=
  negIso ℤ ℤ (rankOneLattice 1)

end Witnesses

@[simp]
theorem negIso_apply (L : LatticeCat R W) (x : L.obj.carrier) :
    BilinModuleCat.underlyingMap ((negIso R W L).hom.hom) x = -x := rfl

@[simp]
theorem reflIso_apply (L : LatticeCat R W) (x : L.obj.carrier) :
    BilinModuleCat.underlyingMap ((Iso.refl L).hom.hom) x = x := rfl

/-- **The marking fiber is a subsingleton exactly when the automorphism group of the reference
lattice is trivial.** With one marking in hand, the markings of `L` are in bijection with the
isometries of `Λ`, so the fiber is contractible-when-inhabited only in the degenerate case. Over a
reference lattice with a nontrivial isometry — the K3 lattice, whose `O(L_K3)` is enormous — it is
not, which is why every consumer of a marked object names its section. -/
theorem markingFibre_subsingleton_iff {Λ L : LatticeCat R W}
    (η₀ : MarkedLatticeCat.markingFibre Λ L) :
    Subsingleton (MarkedLatticeCat.markingFibre Λ L) ↔ Subsingleton (Λ ≅ Λ) := by
  constructor
  · intro h
    refine Subsingleton.intro (fun a b => ?_)
    have hinj : Function.Injective (fun g : Λ ≅ Λ => g ≪≫ η₀) := by
      intro x y hxy
      have hx := congrArg (fun k => k ≪≫ η₀.symm) hxy
      simpa using hx
    exact hinj (h.elim _ _)
  · intro h
    refine ⟨fun η η' => ?_⟩
    obtain ⟨g, hg, -⟩ := MarkedLatticeCat.existsUnique_marking_factor η η'
    rw [h.elim g (Iso.refl Λ)] at hg
    simpa using hg.symm

/-- A torsion-free integral lattice with a nonzero vector carries two distinct markings by itself:
`id` and `−id`. This is the nontrivial case of `markingFibre_subsingleton_iff`. -/
theorem negIso_ne_refl {L : LatticeCat ℤ ℤ}
    (h2 : ∀ y : L.obj.carrier, (2 : ℤ) • y = 0 → y = 0)
    (x : L.obj.carrier) (hx : x ≠ 0) : negIso ℤ ℤ L ≠ Iso.refl L := by
  intro h
  have h3 : BilinModuleCat.underlyingMap ((negIso ℤ ℤ L).hom.hom) x
      = BilinModuleCat.underlyingMap ((Iso.refl L).hom.hom) x :=
    congrArg (fun e => BilinModuleCat.underlyingMap (e.hom.hom) x) h
  rw [reflIso_apply, negIso_apply] at h3
  have hxx : x + x = 0 := by
    nth_rewrite 1 [← h3]
    exact neg_add_cancel x
  exact hx (h2 x (by rw [two_zsmul]; exact hxx))

/-! ## 3. `BC₂` involution actions and the `(−1)` change-of-value-module functor -/

/-- The group `C₂`; its one-object groupoid is `BC₂`, the source of an involution action
(`FOUNDATIONS.md` Definition 28.4). -/
abbrev BC2 : Type := Multiplicative (ZMod 2)

/-- The two elements of `C₂`: every element is the identity or the generator. -/
theorem bc2_eq_one_or_gen (g : BC2) : g = 1 ∨ g = Multiplicative.ofAdd 1 := by
  revert g
  decide

/-- An action of `BC₂` on a lattice, i.e. a functor `BC₂ → Lat_R^≃` (`FOUNDATIONS.md`
Definition 28.4, as amended by the foundations audit: the action lands in the core). -/
abbrev BC2Action := Action (LatticeCore R W) BC2

namespace BC2Action

variable {R W}

/-- The law of a `BC₂`-action: the generator of `C₂` acts by an endomorphism of the lattice whose
square is the identity. `FOUNDATIONS.md` Definition 28.4 records `σ² = 1` as the *equivalent* form
a `C₂`-action; here it is derived from the functor laws and from `2 = 0` in `C₂`, so the two forms
agree on the functorial side. The endomorphism is an automorphism because the action lands in the
core, where every morphism is invertible. -/
theorem gen_sq (A : BC2Action R W) :
    A.ρ (Multiplicative.ofAdd 1) * A.ρ (Multiplicative.ofAdd 1) = 1 := by
  have hgen : (Multiplicative.ofAdd 1 : BC2) * Multiplicative.ofAdd 1 = 1 := by decide
  rw [← map_mul, hgen, map_one]

end BC2Action

/-- The value of the pairing after a change of value module. -/
theorem changeValue_pairing {W' : Type u} [AddCommGroup W'] [Module R W']
    (f : W →ₗ[R] W') (L : LatticeCat R W) (x y : L.obj.carrier) :
    ((changeValue R W f).obj L).obj.pairing x y = f (L.obj.pairing x y) :=
  rfl

/-- The `(−1)` change-of-value-module functor on `Lat_R`: the mechanism behind anti-isometries,
homed in lean-categories#101. -/
def negValueChange : LatticeCat R W ⥤ LatticeCat R W :=
  changeValue R W (-LinearMap.id : W →ₗ[R] W)

/-- Changing the value module along the identity is the identity functor on `Lat_R`. -/
theorem changeValue_id_functor :
    changeValue R W (LinearMap.id : W →ₗ[R] W) = 𝟭 (LatticeCat R W) := rfl

/-- Successive value changes of lattices equal the change along the composite: the value-module
assignment is a functor out of the arrow category of modules. -/
theorem changeValue_comp_functor {W' W'' : Type u} [AddCommGroup W'] [Module R W']
    [AddCommGroup W''] [Module R W''] (f : W →ₗ[R] W') (g : W' →ₗ[R] W'') :
    changeValue R W (g.comp f) = changeValue R W f ⋙ changeValue R W' g := rfl

/-- The `(−1)`-twist is an involution of `Lat_R`: its square is the identity functor. -/
theorem negValueChange_comp_self :
    negValueChange R W ⋙ negValueChange R W = 𝟭 (LatticeCat R W) := by
  change changeValue R W ((-LinearMap.id : W →ₗ[R] W).comp (-LinearMap.id : W →ₗ[R] W)) =
    𝟭 (LatticeCat R W)
  rw [show (-LinearMap.id : W →ₗ[R] W).comp (-LinearMap.id : W →ₗ[R] W) = LinearMap.id from by
      ext x
      simp,
    changeValue_id_functor]

/-- The pairing of the `(−1)`-twisted lattice is the negated pairing. -/
theorem negValueChange_pairing (L : LatticeCat R W) (x y : L.obj.carrier) :
    ((negValueChange R W).obj L).obj.pairing x y = -(L.obj.pairing x y) := by
  have h := changeValue_pairing (R := R) (W := W) (-LinearMap.id : W →ₗ[R] W) L x y
  change ((changeValue R W (-LinearMap.id : W →ₗ[R] W)).obj L).obj.pairing x y =
    -(L.obj.pairing x y)
  rw [h]
  rfl

/-- **The anti-isometry mechanism, stated as an identification.** An anti-isometry — a linear map
`φ` with `q₂(φx) = −q₁(x)`, `FOUNDATIONS.md` Definition 27.5 (Nikulin 1980 §4°) — is exactly an
isometry `φ : L₁ → (−1)·L₂` into the `(−1)` change-of-value-module twist. The sign is not a
convention laid on top of isometries; it is the value-module functor of lean-categories#101. -/
theorem isometry_neg_iff {L₁ L₂ : LatticeCat R W}
    (φ : L₁.obj.carrier →ₗ[R] L₂.obj.carrier) :
    (∀ x y, L₂.obj.pairing (φ x) (φ y) = -L₁.obj.pairing x y) ↔
      ∀ x y, ((negValueChange R W).obj L₂).obj.pairing (φ x) (φ y) =
        L₁.obj.pairing x y := by
  constructor
  · intro h x y
    rw [negValueChange_pairing, h x y, neg_neg]
  · intro h x y
    have hx := h x y
    rw [negValueChange_pairing] at hx
    exact neg_eq_iff_eq_neg.mp hx

/-- Two anti-isometries compose to an isometry — the consequence of `negValueChange_comp_self` that
makes the `(−1)`-twist the right name for the mechanism. -/
theorem antiIsometry_comp {L₁ L₂ L₃ : LatticeCat R W}
    (φ : L₁.obj.carrier →ₗ[R] L₂.obj.carrier)
    (ψ : L₂.obj.carrier →ₗ[R] L₃.obj.carrier)
    (hφ : ∀ x y, L₂.obj.pairing (φ x) (φ y) = -L₁.obj.pairing x y)
    (hψ : ∀ x y, L₃.obj.pairing (ψ x) (ψ y) = -L₂.obj.pairing x y) :
    ∀ x y, L₃.obj.pairing ((ψ.comp φ) x) ((ψ.comp φ) y) = L₁.obj.pairing x y := by
  intro x y
  simp only [LinearMap.comp_apply]
  rw [hψ, hφ, neg_neg]

end LeanCategories.Lattices.Valued

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Extensions of Modules and the Baer Sum

Weibel, *An Introduction to Homological Algebra*, §3.4 (pp. 76–80).

An **extension of `B` by `A`** (Def. 3.4.1) is a short exact sequence
of `R`-modules

  0 → A → E → B → 0.

Two extensions are **equivalent** if there is a morphism of short
complexes that is the identity on `A` and `B`. The **Baer sum** (Def.
3.4.4) makes the equivalence classes into an abelian group
`Ext¹(B, A)`, naturally isomorphic to the derived-functor Ext group.

This file provides:
* `Extension A B` — the type of extensions of `B` by `A`.
* `Extension.Equiv` — equivalence of extensions.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits

/-- An **extension of `B` by `A`** (Weibel, Def. 3.4.1) is a short exact
    sequence `0 → A → E → B → 0` in the category of `R`-modules.

    We package this as a short complex that is short exact, together with
    the proof that its left and right terms are `A` and `B`. -/
structure Extension.{u} {R : Type u} [Ring R] (A B : ModuleCat.{u, u} R) where
  /-- The middle term of the extension. -/
  E : ModuleCat.{u, u} R
  /-- The underlying short complex. -/
  seq : ShortComplex (ModuleCat.{u, u} R)
  /-- The sequence is short exact. -/
  exact : seq.ShortExact
  /-- The left term is `A`. -/
  left_eq : seq.X₁ = A
  /-- The right term is `B`. -/
  right_eq : seq.X₃ = B

namespace Extension

/-- The actual middle object of the short exact sequence underlying an extension.

The legacy `Extension.E` field is not tied to `seq.X₂`; constructions should use
`middle` instead. -/
abbrev middle {R : Type u} [Ring R] {A B : ModuleCat.{u, u} R}
    (e : Extension A B) : ModuleCat.{u, u} R :=
  e.seq.X₂

/-- The endpoint-normalized injection `A ⟶ e.middle`. -/
def leftMap {R : Type u} [Ring R] {A B : ModuleCat.{u, u} R}
    (e : Extension A B) : A ⟶ e.middle :=
  eqToHom e.left_eq.symm ≫ e.seq.f

/-- The endpoint-normalized projection `e.middle ⟶ B`. -/
def rightMap {R : Type u} [Ring R] {A B : ModuleCat.{u, u} R}
    (e : Extension A B) : e.middle ⟶ B :=
  e.seq.g ≫ eqToHom e.right_eq

@[reassoc (attr := simp)]
theorem leftMap_comp_rightMap {R : Type u} [Ring R]
    {A B : ModuleCat.{u, u} R} (e : Extension A B) :
    e.leftMap ≫ e.rightMap = 0 := by
  simp [leftMap, rightMap, Category.assoc]

/-- The underlying short exact sequence with its endpoints normalized to `A` and `B`. -/
def normalizedSeq {R : Type u} [Ring R] {A B : ModuleCat.{u, u} R}
    (e : Extension A B) : ShortComplex (ModuleCat.{u, u} R) :=
  ShortComplex.mk e.leftMap e.rightMap e.leftMap_comp_rightMap

/-- The stored short complex of an extension is canonically isomorphic to its endpoint-normalized
form. -/
def normalizedIso {R : Type u} [Ring R] {A B : ModuleCat.{u, u} R}
    (e : Extension A B) : e.seq ≅ e.normalizedSeq :=
  ShortComplex.isoMk (eqToIso e.left_eq) (Iso.refl _) (eqToIso e.right_eq)
    (by simp [normalizedSeq, leftMap])
    (by simp [normalizedSeq, rightMap])

/-- Endpoint normalization preserves short exactness. -/
theorem normalizedSeq_shortExact {R : Type u} [Ring R]
    {A B : ModuleCat.{u, u} R} (e : Extension A B) :
    e.normalizedSeq.ShortExact :=
  ShortComplex.shortExact_of_iso e.normalizedIso e.exact

theorem leftMap_injective {R : Type u} [Ring R] {A B : ModuleCat.{u, u} R}
    (e : Extension A B) : Function.Injective e.leftMap :=
  CategoryTheory.ShortComplex.ShortExact.moduleCat_injective_f e.normalizedSeq_shortExact

theorem rightMap_surjective {R : Type u} [Ring R] {A B : ModuleCat.{u, u} R}
    (e : Extension A B) : Function.Surjective e.rightMap :=
  CategoryTheory.ShortComplex.ShortExact.moduleCat_surjective_g e.normalizedSeq_shortExact

theorem leftMap_rightMap_exact {R : Type u} [Ring R]
    {A B : ModuleCat.{u, u} R} (e : Extension A B) :
    Function.Exact e.leftMap e.rightMap :=
  (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact e.normalizedSeq).mp
    e.normalizedSeq_shortExact.exact

/-! ### Baer sum -/

/-- The difference of the two quotient maps. Its kernel is the pullback/fibre product over `B`. -/
def baerDifference {R : Type u} [Ring R] {A B : ModuleCat.{u, u} R}
    (e₁ e₂ : Extension A B) :
    (e₁.middle × e₂.middle) →ₗ[R] B where
  toFun x := e₁.rightMap x.1 - e₂.rightMap x.2
  map_add' x y := by
    change e₁.rightMap (x.1 + y.1) - e₂.rightMap (x.2 + y.2) =
      (e₁.rightMap x.1 - e₂.rightMap x.2) +
        (e₁.rightMap y.1 - e₂.rightMap y.2)
    rw [map_add, map_add]
    abel
  map_smul' r x := by
    change e₁.rightMap (r • x.1) - e₂.rightMap (r • x.2) =
      r • (e₁.rightMap x.1 - e₂.rightMap x.2)
    rw [map_smul, map_smul, smul_sub]

/-- The pullback of the two extension projections over their common right endpoint. -/
abbrev baerFiber {R : Type u} [Ring R] {A B : ModuleCat.{u, u} R}
    (e₁ e₂ : Extension A B) : Type u :=
  LinearMap.ker (baerDifference e₁ e₂)

/-- The skew diagonal `a ↦ (i₁(a), -i₂(a))` inside the Baer fibre product. -/
def baerSkew {R : Type u} [Ring R] {A B : ModuleCat.{u, u} R}
    (e₁ e₂ : Extension A B) : A →ₗ[R] baerFiber e₁ e₂ where
  toFun a :=
    ⟨(e₁.leftMap a, -e₂.leftMap a), by
      have h₁ : e₁.rightMap (e₁.leftMap a) = 0 := by
        exact e₁.leftMap_rightMap_exact.apply_apply_eq_zero a
      have h₂ : e₂.rightMap (e₂.leftMap a) = 0 := by
        exact e₂.leftMap_rightMap_exact.apply_apply_eq_zero a
      change e₁.rightMap (e₁.leftMap a) - e₂.rightMap (-e₂.leftMap a) = 0
      simp [h₁, h₂]⟩
  map_add' a a' := by
    apply Subtype.ext
    apply Prod.ext
    · simp
    · simpa using add_comm (-(e₂.leftMap a')) (-(e₂.leftMap a))
  map_smul' r a := by
    apply Subtype.ext
    ext <;> simp

theorem baerSkew_injective {R : Type u} [Ring R] {A B : ModuleCat.{u, u} R}
    (e₁ e₂ : Extension A B) : Function.Injective (baerSkew e₁ e₂) := by
  intro a a' h
  apply e₁.leftMap_injective
  exact congrArg (fun z : baerFiber e₁ e₂ => z.1.1) h

/-- The skew-diagonal submodule by which the fibre product is quotiented. -/
abbrev baerSkewRange {R : Type u} [Ring R] {A B : ModuleCat.{u, u} R}
    (e₁ e₂ : Extension A B) : Submodule R (baerFiber e₁ e₂) :=
  LinearMap.range (baerSkew e₁ e₂)

/-- The middle module of the Baer sum: fibre product modulo the skew diagonal. -/
abbrev baerMiddle {R : Type u} [Ring R] {A B : ModuleCat.{u, u} R}
    (e₁ e₂ : Extension A B) : Type u :=
  baerFiber e₁ e₂ ⧸ baerSkewRange e₁ e₂

/-- Two extensions `0 → A → E₁ → B → 0` and `0 → A → E₂ → B → 0`
    are **equivalent** (Weibel, Def. 3.4.1) if there exists a morphism of
    short complexes `τ : seq₁ → seq₂` with `τ.τ₁ = 𝟙 A` and
    `τ.τ₃ = 𝟙 B`. By the five lemma, `τ.τ₂` is then an isomorphism. -/
structure Equiv.{u} {R : Type u} [Ring R] {A B : ModuleCat.{u, u} R}
    (e₁ e₂ : Extension A B) where
  /-- The underlying morphism of short complexes. -/
  τ : e₁.seq ⟶ e₂.seq
  /-- The left component is the identity on `A` (transported through the
      endpoint equalities). -/
  τ₁_eq : τ.τ₁ =
    eqToHom e₁.left_eq ≫ eqToHom e₂.left_eq.symm
  /-- The right component is the identity on `B` (transported through the
      endpoint equalities). -/
  τ₃_eq : τ.τ₃ =
    eqToHom e₁.right_eq ≫ eqToHom e₂.right_eq.symm

end Extension

end LeanCategories.Homological

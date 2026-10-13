/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# The Roos complex

Weibel, *An Introduction to Homological Algebra*, Vista 3.5.12 (FC05-C03-U059).
For a poset `I` and an inverse system `A : Iᵒᵖ ⥤ C`, the Roos cosimplicial
replacement has in degree `n` the product of `A (i₀)` over all chains
`i₀ ≤ ... ≤ iₙ` in `I`. Its alternating coface complex is the Roos cochain complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace LeanCategories.Homological.Roos

universe u v w

/-- A weakly increasing `n`-chain in a preorder. -/
abbrev Chain (I : Type u) [Preorder I] (n : ℕ) := Fin (n + 1) →o I

/-- Restrict a chain along a simplex morphism. -/
def pullbackChain {I : Type u} [Preorder I] {n m : SimplexCategory}
    (f : n ⟶ m) (c : Chain I m.len) : Chain I n.len :=
  c.comp f.toOrderHom

@[simp] theorem pullbackChain_apply {I : Type u} [Preorder I]
    {n m : SimplexCategory} (f : n ⟶ m) (c : Chain I m.len)
    (i : Fin (n.len + 1)) :
    pullbackChain f c i = c (f.toOrderHom i) := rfl

/-- The order morphism from the first vertex of a chain to the first vertex after restriction. -/
def initialHom {I : Type u} [Preorder I] {n m : SimplexCategory}
    (f : n ⟶ m) (c : Chain I m.len) :
    c 0 ⟶ pullbackChain f c 0 :=
  homOfLE (c.monotone (Fin.zero_le _))

variable {I : Type u} [Preorder I]
variable {C : Type v} [Category.{w} C] [HasProducts.{u} C]

/-- The degree-`n` object in the Roos cosimplicial replacement. -/
noncomputable abbrev term (A : Iᵒᵖ ⥤ C) (n : ℕ) : C :=
  ∏ᶜ fun c : Chain I n => A.obj (op (c 0))

/-- The Roos cosimplicial replacement of an inverse system over a preorder. -/
noncomputable def cosimplicialObject (A : Iᵒᵖ ⥤ C) : CosimplicialObject C where
  obj n := term A n.len
  map {n m} f := Pi.lift fun c : Chain I m.len =>
    Pi.π (fun d : Chain I n.len => A.obj (op (d 0))) (pullbackChain f c) ≫
      A.map (initialHom f c).op
  map_id n := by
    apply Pi.hom_ext
    intro c
    simp only [Category.assoc, Pi.lift_π]
    have hc : pullbackChain (𝟙 n) c = c := by
      ext i
      rfl
    cases hc
    have hinit : initialHom (𝟙 n) c = 𝟙 (c 0) := Subsingleton.elim _ _
    rw [hinit, op_id, A.map_id, Category.comp_id]
  map_comp f g := by
    apply Pi.hom_ext
    intro c
    simp only [Category.assoc, Pi.lift_π]
    have hc : pullbackChain (f ≫ g) c = pullbackChain f (pullbackChain g c) := by
      ext i
      rfl
    cases hc
    rw [← Category.assoc, Pi.lift_π_assoc]
    rw [Category.assoc, ← A.map_comp]
    congr 1
    apply A.map_eq
    apply Quiver.Hom.unop_inj
    apply Subsingleton.elim

end LeanCategories.Homological.Roos

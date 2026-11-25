/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.Presentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-!
# A3's evidence clause, decided by the issue's own example

Issue #99's corrected pullback bullet (comment 6476290045) says a strict pullback of categories
always exists, that an isofibration leg is only a *sufficient* condition for the strict pullback to
agree with the iso-comma, and that the two constructions are therefore not interchangeable. Mathlib
at this pin has no `IsIsoFibration` and no `IsoComma` declaration, but it has the objects: its
`CategoricalPullback F G` is the category of triples `(a, c, F a ≅ G c)`
(`Mathlib/CategoryTheory/Limits/Shapes/Pullback/Categorical/Basic.lean:81-88`), i.e. the iso-comma,
and the strict pullback is the type of pairs with equal images.

This module formalises the issue's own counterexample: the two point selections
`1 → Indiscrete Bool` are not isofibrations, their strict pullback is empty, and their iso-comma is
inhabited — so no equivalence relates them, and an isofibration cannot be a prerequisite for a
strict pullback's existence or a replacement for classifying a row directly.
-/

@[expose] public section

namespace CasCatalogue

open CategoryTheory

/-- The indiscrete category on `α`: exactly one arrow between any two objects. -/
def Indiscrete (α : Type) : Type := α

namespace Indiscrete

instance instCategoryStruct (α : Type) : CategoryStruct (Indiscrete α) where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

instance instCategory (α : Type) : Category (Indiscrete α) where
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The unique isomorphism between two objects of an indiscrete category. -/
def iso {α : Type} (a b : Indiscrete α) : a ≅ b where
  hom := PUnit.unit
  inv := PUnit.unit
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The functor out of the terminal category picking the object `a`. -/
def point {α : Type} (a : α) : Discrete PUnit ⥤ Indiscrete α where
  obj _ := a
  map _ := PUnit.unit
  map_id _ := rfl
  map_comp _ _ := rfl

end Indiscrete

/-- The objects of the strict pullback of two functors: pairs with **equal** images. -/
def StrictPullbackObjects {A B C : Type} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : C ⥤ B) : Type :=
  {p : A × C // F.obj p.1 = G.obj p.2}

/-- An isofibration lifts isomorphisms: an isomorphism out of `F.obj a` is the image of one out of
`a`, landing at the required object. -/
def IsIsoFibration {A B : Type} [Category A] [Category B] (F : A ⥤ B) : Prop :=
  ∀ ⦃a : A⦄ ⦃b : B⦄, (F.obj a ≅ b) → ∃ (a' : A) (_ : a ≅ a'), F.obj a' = b

/-- The strict pullback of the two point selections into the indiscrete category is empty: no pair
of points has `false` equal to `true`. -/
theorem strictPullback_isEmpty :
    IsEmpty (StrictPullbackObjects (A := Discrete PUnit) (B := Indiscrete Bool)
      (C := Discrete PUnit) (Indiscrete.point (false : Bool)) (Indiscrete.point true)) :=
  ⟨fun p => Bool.false_ne_true p.2⟩

/-- Their iso-comma is inhabited: the two selected objects are isomorphic in the indiscrete
category, so the triple is an object of `CategoricalPullback`. -/
def isoCommaPoint :
    Limits.CategoricalPullback (Indiscrete.point (false : Bool)) (Indiscrete.point true) :=
  ⟨Discrete.mk PUnit.unit, Discrete.mk PUnit.unit, Indiscrete.iso false true⟩

/-- A point selection into the indiscrete category is not an isofibration: the isomorphism
`false ≅ true` cannot be lifted, since every object is sent to `false`. -/
theorem point_not_isofibration : ¬ IsIsoFibration (Indiscrete.point (false : Bool)) := by
  intro hfibration
  obtain ⟨source, iso, himage⟩ :=
    hfibration (a := Discrete.mk PUnit.unit) (b := true) (Indiscrete.iso false true)
  exact Bool.false_ne_true himage

/-- The issue's own example (comment 6476290045), at the legs `1 → Indiscrete Bool` picking
`false` and `true`: the leg is **not** an isofibration, the strict pullback has no object, and the
iso-comma has one (`isoCommaPoint`). The two constructions therefore differ at these legs, so an
isofibration is neither a prerequisite for the strict pullback nor a licence to read one as the
other; a row states its kind, which is what `PullbackKind` records. -/
theorem strict_and_isoComma_differ :
    IsEmpty (StrictPullbackObjects (A := Discrete PUnit) (B := Indiscrete Bool)
      (C := Discrete PUnit) (Indiscrete.point (false : Bool)) (Indiscrete.point true)) ∧
      ¬ IsIsoFibration (Indiscrete.point (false : Bool)) :=
  ⟨strictPullback_isEmpty, point_not_isofibration⟩

end CasCatalogue

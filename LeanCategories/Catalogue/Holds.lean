/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryTheory.OneCat.Classifier
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

/-!
# The property query of a classifier (CC-PROP)

A property is a classifier `p : 𝒞.A → 𝒞`. The query "does `X` have `A`" asks whether the fibre of
`p` over `X` is inhabited (FOUNDATIONS Def. 46.4). Deciding it on a presentation is a realization's
business (`lean-cas-dsl`'s `Decider`).
-/

open CategoryTheory

namespace CasCatalogue

universe uObj uHom

/-- The property query of FOUNDATIONS Def. 46.4: the fibre of the classifier over `X` is
inhabited. -/
def Classifier.Holds {C : LeanCategories.ObjCat.{uObj, uHom}} (c : LeanCategories.Classifier C)
    (X : C) : Prop :=
  Nonempty (c.forget.toFunctor.Fiber X)


/-- The fibre of the classifier of a property over `X` is inhabited iff `X` has the property: for a
property classifier, the registered decision of `Holds` is a decision of `P`. -/
theorem Classifier.holds_ofProperty {C : LeanCategories.ObjCat.{uObj, uHom}} (P : ObjectProperty C)
    (X : C) : Classifier.Holds (LeanCategories.Classifier.ofProperty P) X ↔ P X :=
  ⟨fun ⟨⟨Y, e⟩⟩ => e ▸ Y.property, fun h => ⟨⟨⟨X, h⟩, rfl⟩⟩⟩


end CasCatalogue

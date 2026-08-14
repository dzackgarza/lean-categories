/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryTheory.OneCat.Universes
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

/-!
# Singleton categories

The category `{R}` is Mathlib's full subcategory for the singleton object
property. Its membership functor is the fully faithful inclusion into `C`.
-/

namespace LeanCategories

open CategoryTheory

universe v u

/-- The one-object full subcategory `{R}` of a category `C`. -/
abbrev OneObjectCat (C : Type u) [Category.{v} C] (R : C) : Type u :=
  (ObjectProperty.singleton R).FullSubcategory

/-- The membership, or underlying-object, functor `{R} ⥤ C`. -/
abbrev membershipFunctor (C : Type u) [Category.{v} C] (R : C) :
    OneObjectCat C R ⥤ C :=
  (ObjectProperty.singleton R).ι

end LeanCategories

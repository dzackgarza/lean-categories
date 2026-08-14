/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Presentation.Basic

@[expose] public section

namespace LeanCategories.Modules

open CategoryTheory

universe u v w₀ w₁

variable (R : Type u) [Ring R]

/-- A module equipped with a chosen generators-and-relations presentation. -/
structure PresentedModule where
  carrier : ModuleCat.{v} R
  presentation : Module.Presentation.{w₀, w₁} R carrier

/-- Modules carrying a chosen presentation, with abstract module maps as morphisms. -/
abbrev PresentedModules := PresentedModule

namespace PresentedModules

variable {R}

/-- The carrier module of a presented-module object. -/
abbrev carrierObj (X : PresentedModules R) : ModuleCat.{v} R := X.carrier

instance : Category.{max u v} (PresentedModules R) where
  Hom X Y := X.carrierObj ⟶ Y.carrierObj
  id X := 𝟙 X.carrierObj
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

/-- Forget the chosen presentation and retain the carrier module. -/
def forget : PresentedModules R ⥤ ModuleCat.{v} R where
  obj X := X.carrierObj
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (forget (R := R)).Faithful where
  map_injective h := h

instance : (forget (R := R)).Full where
  map_surjective f := ⟨f, rfl⟩

end PresentedModules

end LeanCategories.Modules

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Presented
public import LeanCategories.Modules.Quadratic.Valued.Fixed
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

namespace LeanCategories.Modules.Quadratic.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

/-- Quadratic modules equipped with a chosen presentation of their carrier module. -/
abbrev PresentedQuadModuleCat :=
  CategoricalPullback
    (LeanCategories.Modules.PresentedModule.forget (R := R))
    (LeanCategories.Modules.Quadratic.Valued.forget R W)

/-- Forget the quadratic structure and retain the chosen module presentation. -/
def presentedQuadModuleToPresented :
    PresentedQuadModuleCat R W ⥤ LeanCategories.Modules.PresentedModule R :=
  CategoricalPullback.π₁ _ _

/-- Forget the chosen module presentation and retain the quadratic module. -/
def presentedQuadModuleToQuad :
    PresentedQuadModuleCat R W ⥤ QuadModuleCat R W :=
  CategoricalPullback.π₂ _ _

end LeanCategories.Modules.Quadratic.Valued

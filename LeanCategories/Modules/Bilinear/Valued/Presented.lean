/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Fixed
public import LeanCategories.Modules.Presented
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

/-- Bilinear modules with a chosen generators-and-relations presentation of their carrier.

The category is the categorical pullback of the presentation-forgetting functor and the
bilinear-module carrier functor.  Its comparison isomorphism identifies the two carrier
modules, so the presentation and bilinear form are retained as separate data.
-/
abbrev PresentedBilinModuleCat :=
  CategoricalPullback
    (LeanCategories.Modules.PresentedModule.forget (R := R))
    (LeanCategories.Modules.Bilinear.Valued.forget R W)

/-- Forget the bilinear structure and retain the chosen presentation. -/
def presentedBilinModuleToPresented :
    PresentedBilinModuleCat R W ⥤ LeanCategories.Modules.PresentedModule R :=
  CategoricalPullback.π₁ _ _

/-- Forget the chosen presentation and retain the bilinear module. -/
def presentedBilinModuleToBilin :
    PresentedBilinModuleCat R W ⥤ BilinModuleCat R W :=
  CategoricalPullback.π₂ _ _

end LeanCategories.Modules.Bilinear.Valued

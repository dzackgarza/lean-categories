/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Fixed
public import LeanCategories.Modules.Framed
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]
variable (n : ℕ)

/-- Rank-`n` coordinatized `W`-valued formed modules.

An object consists of a selected basis frame, a formed-module structure, and an
isomorphism identifying their carrier modules.  The pullback therefore retains
the mathematical formed module while making its coordinates explicit.
-/
abbrev CoordBilinModuleCat :=
  CategoricalPullback
    (LeanCategories.Modules.Coord.forget R (Fin n))
    (BilinModuleCat.forget R W)

/-- Forget the formed-module structure and retain the selected coordinates. -/
def coordBilinModuleToCoord :
    CoordBilinModuleCat R W n ⥤ LeanCategories.Modules.Coord R (Fin n) :=
  CategoricalPullback.π₁ _ _

/-- Forget the selected coordinates and retain the formed module. -/
def coordBilinModuleToBilin :
    CoordBilinModuleCat R W n ⥤ BilinModuleCat R W :=
  CategoricalPullback.π₂ _ _

end LeanCategories.Modules.Bilinear.Valued

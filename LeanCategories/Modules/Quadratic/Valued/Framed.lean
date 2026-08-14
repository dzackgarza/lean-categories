/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Quadratic.Valued.Fixed
public import LeanCategories.Modules.Framed
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LeanCategories.Modules.Quadratic.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]
variable (n : ℕ)

/-- Rank-`n` coordinatized `W`-valued quadratic modules. -/
abbrev CoordQuadModuleCat :=
  CategoricalPullback
    (LeanCategories.Modules.Coord.forget R (Fin n))
    (LeanCategories.Modules.Quadratic.Valued.forget R W)

/-- Forget the quadratic structure and retain the selected coordinates. -/
def coordQuadModuleToCoord :
    CoordQuadModuleCat R W n ⥤ LeanCategories.Modules.Coord R (Fin n) :=
  CategoricalPullback.π₁ _ _

/-- Forget the selected coordinates and retain the quadratic module. -/
def coordQuadModuleToQuad :
    CoordQuadModuleCat R W n ⥤ QuadModuleCat R W :=
  CategoricalPullback.π₂ _ _

end LeanCategories.Modules.Quadratic.Valued

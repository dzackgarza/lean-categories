/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Total
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable (R : Type u) [CommRing R]

/-- Symmetric objects in the total category of variable-valued forms. -/
def isSymmetricBilWForm : ObjectProperty (BilWFormCat R) :=
  fun X ↦ X.IsSymmetric

/-- The total category of symmetric forms with variable value modules. -/
abbrev SymBilWFormCat := (isSymmetricBilWForm R).FullSubcategory

/-- Skew-symmetric objects in the total category of variable-valued forms. -/
def isSkewSymmetricBilWForm : ObjectProperty (BilWFormCat R) :=
  fun X ↦ X.IsSkewSymmetric

/-- The total category of skew-symmetric forms with variable value modules. -/
abbrev SkewBilWFormCat := (isSkewSymmetricBilWForm R).FullSubcategory

/-- Alternating objects in the total category of variable-valued forms. -/
def isAlternatingBilWForm : ObjectProperty (BilWFormCat R) :=
  fun X ↦ X.IsAlternating

/-- The total category of alternating forms with variable value modules. -/
abbrev AltBilWFormCat := (isAlternatingBilWForm R).FullSubcategory

end LeanCategories.Modules.Bilinear.Valued


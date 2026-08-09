/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Fixed
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

open CategoryTheory

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

/-- Finitely generated torsion modules with a fixed-value bilinear form. -/
def isFiniteTorsionBilinModule : ObjectProperty (BilinModuleCat R W) :=
  fun A ↦ Module.Finite R A.carrier ∧ Module.IsTorsion R A.carrier

/-- The category of finitely generated torsion bilinear modules. -/
abbrev FiniteTorsionBilinModuleCat :=
  (isFiniteTorsionBilinModule R W).FullSubcategory

/-- Finite torsion bilinear modules with symmetric form. -/
def isFiniteTorsionSymBilinModule : ObjectProperty (BilinModuleCat R W) :=
  fun A ↦ Module.Finite R A.carrier ∧
    Module.IsTorsion R A.carrier ∧ A.IsSymmetric

/-- The category of finite torsion symmetric bilinear modules. -/
abbrev FiniteTorsionSymBilinModuleCat :=
  (isFiniteTorsionSymBilinModule R W).FullSubcategory

/-- Perfect finite torsion symmetric bilinear modules. -/
def isNonsingularFiniteTorsionBilinModule :
    ObjectProperty (BilinModuleCat R W) :=
  fun A ↦ Module.Finite R A.carrier ∧
    Module.IsTorsion R A.carrier ∧ A.IsSymmetric ∧ A.IsPerfect

/-- The category of nonsingular finite torsion symmetric bilinear modules. -/
abbrev NonsingularFiniteTorsionBilinModuleCat :=
  (isNonsingularFiniteTorsionBilinModule R W).FullSubcategory

end LeanCategories.Modules.Bilinear.Valued

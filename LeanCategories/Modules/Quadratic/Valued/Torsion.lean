/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Quadratic.Valued.Fixed
public import LeanCategories.Modules.Quadratic.Valued.OrthogonalGroup
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

open CategoryTheory

namespace LeanCategories.Modules.Quadratic.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

/-- Finitely generated torsion modules with a fixed-value quadratic map. -/
def isFiniteTorsionQuadModule : ObjectProperty (QuadModuleCat R W) :=
  fun A ↦ Module.Finite R A.carrier ∧ Module.IsTorsion R A.carrier

/-- The category of finitely generated torsion quadratic modules. -/
abbrev FiniteTorsionQuadModuleCat :=
  (isFiniteTorsionQuadModule R W).FullSubcategory

/-- Perfect finite torsion quadratic modules. -/
def isNonsingularFiniteTorsionQuadModule :
    ObjectProperty (QuadModuleCat R W) :=
  fun A ↦ Module.Finite R A.carrier ∧
    Module.IsTorsion R A.carrier ∧ A.IsPerfect

/-- The category of nonsingular finite torsion quadratic modules. -/
abbrev NonsingularFiniteTorsionQuadModuleCat :=
  (isNonsingularFiniteTorsionQuadModule R W).FullSubcategory

end LeanCategories.Modules.Quadratic.Valued

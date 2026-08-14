/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Quadratic.Valued.Total
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace LeanCategories.Modules.Quadratic.Valued

universe u

variable (R : Type u) [CommRing R]

namespace QuadModuleCat

variable {R W} [AddCommGroup W] [Module R W]

/-- The module of linear maps from a quadratic-module carrier to its value module. -/
abbrev valueDual (Q : QuadModuleCat R W) := Q.carrier →ₗ[R] W

/-- The cokernel of the polar adjoint. -/
abbrev defect (Q : QuadModuleCat R W) :=
  Q.valueDual ⧸ LinearMap.range Q.polarAdjoint

/-- The quotient projection onto the quadratic defect. -/
def defectProjection (Q : QuadModuleCat R W) :
    Q.valueDual →ₗ[R] Q.defect :=
  Submodule.mkQ (LinearMap.range Q.polarAdjoint)

theorem exact_polarAdjoint_defect (Q : QuadModuleCat R W) :
    Function.Exact Q.polarAdjoint Q.defectProjection :=
  LinearMap.exact_map_mkQ_range Q.polarAdjoint

theorem defectProjection_surjective (Q : QuadModuleCat R W) :
    Function.Surjective Q.defectProjection :=
  Submodule.mkQ_surjective _

end QuadModuleCat

namespace QuadWFormCat

variable {R}

/-- The polar adjoint of a total quadratic formed module. -/
abbrev polarAdjoint (X : QuadWFormCat R) := X.formed.polarAdjoint

/-- The value dual of a total quadratic formed module. -/
abbrev valueDual (X : QuadWFormCat R) := X.formed.valueDual

/-- The defect of a total quadratic formed module. -/
abbrev defect (X : QuadWFormCat R) := X.formed.defect

/-- The defect projection of a total quadratic formed module. -/
abbrev defectProjection (X : QuadWFormCat R) := X.formed.defectProjection

end QuadWFormCat

end LeanCategories.Modules.Quadratic.Valued

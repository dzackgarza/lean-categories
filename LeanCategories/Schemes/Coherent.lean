/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace LeanCategories.Schemes

universe u

variable (X : Scheme.{u})

/-- Sheaves of modules that admit finite-presentation quasi-coherent data. -/
def isCoherentModule : ObjectProperty X.Modules :=
  fun M => ∃ q : M.QuasicoherentData, q.IsFinitePresentation

/-- Coherent sheaves of modules on `X`. -/
abbrev CoherentModuleCat := (isCoherentModule X).FullSubcategory

/-- The inclusion of coherent modules into all sheaves of modules. -/
abbrev coherentModuleIncl : CoherentModuleCat X ⥤ X.Modules :=
  (isCoherentModule X).ι

end LeanCategories.Schemes

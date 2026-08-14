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

/-- Coherent sheaves of modules on `X`. -/
abbrev CoherentModuleCat :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).FullSubcategory

/-- The inclusion of coherent modules into all sheaves of modules. -/
abbrev coherentModuleIncl : CoherentModuleCat X ⥤ X.Modules :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι

end LeanCategories.Schemes

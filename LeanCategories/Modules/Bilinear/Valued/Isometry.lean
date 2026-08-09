/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Fixed
public import Mathlib.LinearAlgebra.BilinearForm.Isometry

@[expose] public section

open CategoryTheory

namespace LeanCategories.Modules.Bilinear.Valued

universe u

namespace BilinModuleCat

variable {R : Type u} [CommRing R]

/-- Regard an `R`-valued formed module as a Mathlib bilinear form. -/
abbrev asBilinForm (L : BilinModuleCat R R) : LinearMap.BilinForm R L.carrier :=
  L.bilinMap

/-- A formed-module morphism is a Mathlib isometry of the underlying bilinear forms. -/
def toMathlibIsometry {L M : BilinModuleCat R R} (f : L ⟶ M) :
    L.asBilinForm →bᵢ M.asBilinForm where
  __ := underlyingMap f
  map_app' := map_pairing f

/-- Build a formed-module morphism from a Mathlib bilinear-form isometry. -/
def fromMathlibIsometry {L M : BilinModuleCat R R}
    (f : L.asBilinForm →bᵢ M.asBilinForm) : L ⟶ M :=
  homMk f.toLinearMap f.map_app

@[simp]
theorem underlyingMap_fromMathlibIsometry {L M : BilinModuleCat R R}
    (f : L.asBilinForm →bᵢ M.asBilinForm) :
    underlyingMap (fromMathlibIsometry f) = f.toLinearMap :=
  rfl

@[simp]
theorem fromMathlibIsometry_toMathlibIsometry {L M : BilinModuleCat R R}
    (f : L ⟶ M) : fromMathlibIsometry (toMathlibIsometry f) = f := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  apply Quiver.Hom.unop_inj
  apply ModuleCat.hom_ext
  rfl

@[simp]
theorem toMathlibIsometry_fromMathlibIsometry {L M : BilinModuleCat R R}
    (f : L.asBilinForm →bᵢ M.asBilinForm) :
    toMathlibIsometry (fromMathlibIsometry f) = f := by
  apply LinearMap.BilinForm.Isometry.ext
  intro x
  rfl

end BilinModuleCat

end LeanCategories.Modules.Bilinear.Valued

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

namespace CoordQuadModuleCat

/-! A coordinate frame transports the quadratic map to the standard free module. -/

noncomputable def standardIso (X : CoordQuadModuleCat R W n) :
    ModuleCat.of R (Fin n → R) ≅ X.snd.carrierObj := by
  let e : LeanCategories.Modules.StandardFreeModule R (Fin n) ≅ X.snd.carrierObj :=
    (LeanCategories.Modules.Coord.frameIso R (Fin n) X.fst).trans X.iso
  let b : Module.Basis (Fin n) R X.snd.carrier :=
    Module.Basis.ofRepr e.toLinearEquiv.symm
  exact LinearEquiv.toModuleIso b.equivFun.symm

noncomputable def standardForm (X : CoordQuadModuleCat R W n) :
    QuadraticMap R (Fin n → R) W := by
  let e := (standardIso R W n X).toLinearEquiv
  exact X.snd.form.comp e.toLinearMap

noncomputable def standardMap {X Y : CoordQuadModuleCat R W n} (f : X ⟶ Y) :
    (Fin n → R) →ₗ[R] Fin n → R := by
  let eX := (standardIso R W n X).toLinearEquiv
  let eY := (standardIso R W n Y).toLinearEquiv
  exact eY.symm.toLinearMap.comp
    ((QuadModuleCat.underlyingMap f.snd).comp eX.toLinearMap)

theorem standardMap_preserves_form {X Y : CoordQuadModuleCat R W n}
    (f : X ⟶ Y) (x : Fin n → R) :
    standardForm R W n Y (standardMap R W n f x) =
      standardForm R W n X x := by
  let eX := (standardIso R W n X).toLinearEquiv
  let eY := (standardIso R W n Y).toLinearEquiv
  change Y.snd.form
      (eY (eY.symm (QuadModuleCat.underlyingMap f.snd (eX x)))) =
    X.snd.form (eX x)
  rw [eY.apply_symm_apply]
  exact QuadModuleCat.map_form f.snd (eX x)

/-- Transport the quadratic module to its selected standard coordinates.

This is the exact quadratic codomain of the framed category.  It retains the full quadratic
map; no matrix presentation is silently substituted for the quadratic object. -/
noncomputable def standardQuadraticFunctor :
    CoordQuadModuleCat R W n ⥤ QuadModuleCat R W where
  obj X := QuadModuleCat.ofQuadraticMap (standardForm R W n X)
  map f := QuadModuleCat.homMk (standardMap R W n f) (by
    intro x
    change standardForm R W n Y (standardMap R W n f x) =
      standardForm R W n X x
    exact standardMap_preserves_form R W n f x)
  map_id X := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    ext x
    simp [standardMap, QuadModuleCat.underlyingMap]
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    ext x
    simp [standardMap, QuadModuleCat.underlyingMap]

end CoordQuadModuleCat

end LeanCategories.Modules.Quadratic.Valued

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
  map {X Y} f := QuadModuleCat.homMk (standardMap R W n f) (by
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
    let eX := (standardIso R W n X).toLinearEquiv
    change standardMap R W n (𝟙 X) x = x
    change eX.symm (eX x) = x
    exact eX.symm_apply_apply x
  map_comp {X Y Z} f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    ext x
    let eX := (standardIso R W n X).toLinearEquiv
    let eY := (standardIso R W n Y).toLinearEquiv
    let eZ := (standardIso R W n Z).toLinearEquiv
    change eZ.symm
        (QuadModuleCat.underlyingMap g.snd
          (QuadModuleCat.underlyingMap f.snd (eX x))) =
      eZ.symm
        (QuadModuleCat.underlyingMap g.snd
          (eY (eY.symm (QuadModuleCat.underlyingMap f.snd (eX x)))))
    rw [eY.apply_symm_apply]

/-! Change the selected standard frame by a fixed linear automorphism. -/

noncomputable def changeFrameMap
    (e : (Fin n → R) ≃ₗ[R] (Fin n → R))
    {X Y : CoordQuadModuleCat R W n} (f : X ⟶ Y) :
    (Fin n → R) →ₗ[R] Fin n → R :=
  e.symm.toLinearMap.comp
    ((standardMap R W n f).comp e.toLinearMap)

/-- Reparameterize the standard quadratic realization by a fixed change of frame. -/
noncomputable def changeFrameQuadraticFunctor
    (e : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    CoordQuadModuleCat R W n ⥤ QuadModuleCat R W where
  obj X :=
    QuadModuleCat.ofQuadraticMap
      ((standardForm R W n X).comp e.toLinearMap)
  map {X Y} f := QuadModuleCat.homMk (changeFrameMap R W n e f) (by
    intro x
    change standardForm R W n Y
        (e (e.symm (standardMap R W n f (e x)))) =
      standardForm R W n X (e x)
    rw [e.apply_symm_apply]
    exact standardMap_preserves_form R W n f (e x))
  map_id X := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    ext x
    change changeFrameMap R W n e (𝟙 X) x = x
    let eX := (standardIso R W n X).toLinearEquiv
    change e.symm (eX.symm (eX (e x))) = x
    simp
  map_comp {X Y Z} f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    ext x
    change changeFrameMap R W n e (f ≫ g) x =
      changeFrameMap R W n e g (changeFrameMap R W n e f x)
    simp only [changeFrameMap, LinearMap.comp_apply]
    simp [standardMap, QuadModuleCat.underlyingMap]
    let eY := (standardIso R W n Y).toLinearEquiv
    have hY (z : Y.snd.carrier) :
        (standardIso R W n Y).hom.hom (eY.symm z) = z := by
      change eY (eY.symm z) = z
      exact eY.apply_symm_apply z
    rw [hY]
    rfl

end CoordQuadModuleCat

end LeanCategories.Modules.Quadratic.Valued

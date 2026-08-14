/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Fixed
public import LeanCategories.Modules.Framed
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]
variable (n : ℕ)

/-- Rank-`n` coordinatized `W`-valued formed modules.

An object consists of a selected basis frame, a formed-module structure, and an
isomorphism identifying their carrier modules.  The pullback therefore retains
the mathematical formed module while making its coordinates explicit.
-/
abbrev CoordBilinModuleCat :=
  CategoricalPullback
    (LeanCategories.Modules.Coord.forget R (Fin n))
    (BilinModuleCat.forget R W)

/-- Forget the formed-module structure and retain the selected coordinates. -/
def coordBilinModuleToCoord :
    CoordBilinModuleCat R W n ⥤ LeanCategories.Modules.Coord R (Fin n) :=
  CategoricalPullback.π₁ _ _

/-- Forget the selected coordinates and retain the formed module. -/
def coordBilinModuleToBilin :
    CoordBilinModuleCat R W n ⥤ BilinModuleCat R W :=
  CategoricalPullback.π₂ _ _

namespace CoordBilinModuleCat

/-! Change of presentation by precomposition of the selected basis frame. -/

noncomputable def changeFrameCoord
    (e : LeanCategories.Modules.StandardFreeModule R (Fin n) ≅
      LeanCategories.Modules.StandardFreeModule R (Fin n)) :
    LeanCategories.Modules.Coord R (Fin n) ⥤ LeanCategories.Modules.Coord R (Fin n) where
  obj X :=
    { frame :=
        { obj := StructuredArrow.mk (e.inv ≫ X.frame.obj.hom)
          property := by
            change IsIso (e.inv ≫ X.frame.obj.hom)
            infer_instance } }
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Change the selected coordinates while retaining the intrinsic bilinear module.

The new frame is `e.inv` followed by the old frame.  Since the carrier is unchanged,
the pullback comparison is unchanged and every form-preserving morphism maps to itself.
-/
noncomputable def changeFrameFunctor
    (e : LeanCategories.Modules.StandardFreeModule R (Fin n) ≅
      LeanCategories.Modules.StandardFreeModule R (Fin n)) :
    CoordBilinModuleCat R R n ⥤ CoordBilinModuleCat R R n where
  obj X :=
    { fst := (changeFrameCoord R n e).obj X.fst
      snd := X.snd
      iso := X.iso }
  map f :=
    { fst := f.fst
      snd := f.snd }
  map_id _ := rfl
  map_comp _ _ := rfl

/-! A coordinate form is represented on the standard function module. -/

noncomputable def standardIso (X : CoordBilinModuleCat R R n) :
    ModuleCat.of R (Fin n → R) ≅ X.snd.carrierObj := by
  let e : LeanCategories.Modules.StandardFreeModule R (Fin n) ≅ X.snd.carrierObj :=
    (LeanCategories.Modules.Coord.frameIso R (Fin n) X.fst).trans X.iso
  let b : Module.Basis (Fin n) R X.snd.carrier :=
    Module.Basis.ofRepr e.toLinearEquiv.symm
  exact LinearEquiv.toModuleIso b.equivFun.symm

noncomputable def standardForm (X : CoordBilinModuleCat R R n) :
    LinearMap.BilinForm R (Fin n → R) := by
  let e := (standardIso R n X).toLinearEquiv
  exact X.snd.bilinMap.comp e.toLinearMap e.toLinearMap

/-- The Gram matrix in the selected coordinates. -/
noncomputable def gramMatrix (X : CoordBilinModuleCat R R n) :
    Matrix (Fin n) (Fin n) R :=
  LinearMap.BilinForm.toMatrix' (standardForm R n X)

noncomputable def standardMap {X Y : CoordBilinModuleCat R R n} (f : X ⟶ Y) :
    (Fin n → R) →ₗ[R] Fin n → R := by
  let eX := (standardIso R n X).toLinearEquiv
  let eY := (standardIso R n Y).toLinearEquiv
  exact eY.symm.toLinearMap.comp
    ((BilinModuleCat.underlyingMap f.snd).comp eX.toLinearMap)

theorem standardMap_preserves_form {X Y : CoordBilinModuleCat R R n}
    (f : X ⟶ Y) (x y : Fin n → R) :
    standardForm R n Y (standardMap R n f x) (standardMap R n f y) =
      standardForm R n X x y := by
  let eX := (standardIso R n X).toLinearEquiv
  let eY := (standardIso R n Y).toLinearEquiv
  change Y.snd.pairing
      (eY (eY.symm (BilinModuleCat.underlyingMap f.snd (eX x))))
      (eY (eY.symm (BilinModuleCat.underlyingMap f.snd (eX y)))) =
    X.snd.pairing (eX x) (eX y)
  rw [eY.apply_symm_apply, eY.apply_symm_apply]
  exact BilinModuleCat.map_pairing f.snd (eX x) (eX y)

/-- Extract a Gram matrix and regard it as the corresponding standard formed module.

The codomain is the existing fixed-value formed-module category.  Its objects are standard
coordinate forms, and its morphisms retain the form-preserving coordinate maps. -/
noncomputable def gramMatrixFunctor :
    CoordBilinModuleCat R R n ⥤ BilinModuleCat R R where
  obj X := BilinModuleCat.ofBilinMap (Matrix.toBilin' (gramMatrix R n X))
  map f := BilinModuleCat.homMk (standardMap R n f) (by
    intro x y
    change Matrix.toBilin' (gramMatrix R n Y) (standardMap R n f x)
        (standardMap R n f y) = Matrix.toBilin' (gramMatrix R n X) x y
    simpa only [gramMatrix, Matrix.toBilin'_toMatrix'] using
      standardMap_preserves_form R n f x y)
  map_id X := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    ext x
    simp [standardMap, BilinModuleCat.underlyingMap]
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    ext x
    simp [standardMap, BilinModuleCat.underlyingMap]

end CoordBilinModuleCat

end LeanCategories.Modules.Bilinear.Valued

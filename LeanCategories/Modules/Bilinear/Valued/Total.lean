/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.ChangeValue
public import Mathlib.CategoryTheory.Grothendieck

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable (R : Type u) [CommRing R]

/-- The functor of formed-module categories indexed by their value modules. -/
def valueFibers : ModuleCat.{u} R ⥤ Cat.{u, u + 1} where
  obj W := Cat.of (BilinModuleCat R W)
  map {W _} α := (changeValue R W α.hom).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The category of formed `R`-modules with a variable module of values. -/
abbrev BilWFormCat := Grothendieck (valueFibers R)

namespace BilWFormCat

variable {R}

/-- The value module of a formed module in the total category. -/
abbrev value (X : BilWFormCat R) : ModuleCat R := X.base

/-- The fixed-value formed module underlying an object of the total category. -/
abbrev formed (X : BilWFormCat R) : BilinModuleCat R X.value := X.fiber

/-- The carrier module of a formed module in the total category. -/
abbrev carrier (X : BilWFormCat R) : ModuleCat R := X.formed.carrierObj

/-- The bilinear form of an object in the total category. -/
abbrev form (X : BilWFormCat R) :
    TensorProduct R (X.carrier : Type u) (X.carrier : Type u) →ₗ[R] X.value :=
  X.formed.form

/-- The value of the form on two carrier elements. -/
abbrev pairing (X : BilWFormCat R) (x y : X.carrier) : X.value :=
  X.formed.pairing x y

/-- The left adjoint of a formed module in the total category. -/
abbrev adjoint (X : BilWFormCat R) := X.formed.adjoint

/-- The right adjoint of a formed module in the total category. -/
abbrev rightAdjoint (X : BilWFormCat R) := X.formed.rightAdjoint

/-- The left radical of a formed module in the total category. -/
abbrev leftRadical (X : BilWFormCat R) := X.formed.leftRadical

/-- The right radical of a formed module in the total category. -/
abbrev rightRadical (X : BilWFormCat R) := X.formed.rightRadical

/-- Left nondegeneracy of a formed module in the total category. -/
def IsLeftNondegenerate (X : BilWFormCat R) : Prop :=
  X.formed.bilinMap.SeparatingLeft

/-- Right nondegeneracy of a formed module in the total category. -/
def IsRightNondegenerate (X : BilWFormCat R) : Prop :=
  X.formed.bilinMap.SeparatingRight

/-- Nondegeneracy of a formed module in the total category. -/
def IsNondegenerate (X : BilWFormCat R) : Prop :=
  X.formed.bilinMap.Nondegenerate

/-- Symmetry of a formed module in the total category. -/
def IsSymmetric (X : BilWFormCat R) : Prop :=
  X.formed.IsSymmetric

/-- Skew-symmetry of a formed module in the total category. -/
def IsSkewSymmetric (X : BilWFormCat R) : Prop :=
  X.formed.IsSkewSymmetric

/-- Alternation of a formed module in the total category. -/
def IsAlternating (X : BilWFormCat R) : Prop :=
  X.formed.IsAlternating

/-- Every alternating object in the total category is skew-symmetric. -/
theorem isSkewSymmetric_of_isAlternating (X : BilWFormCat R)
    (hX : X.IsAlternating) : X.IsSkewSymmetric :=
  X.formed.isSkewSymmetric_of_isAlternating hX

/-- The map between value modules underlying a morphism in the total category. -/
abbrev valueMap {X Y : BilWFormCat R} (f : X ⟶ Y) : X.value ⟶ Y.value :=
  f.base

/-- The map between carrier modules underlying a morphism in the total category. -/
abbrev carrierMap {X Y : BilWFormCat R} (f : X ⟶ Y) : X.carrier ⟶ Y.carrier :=
  ModuleCat.ofHom (BilinModuleCat.underlyingMap f.fiber)

/-- Build an object of the total category from its carrier, value module, and form. -/
def of (M W : ModuleCat.{u} R)
    (b : TensorProduct R (M : Type u) (M : Type u) →ₗ[R] W) : BilWFormCat R where
  base := W
  fiber := op ⟨op M, b⟩

/-- Build a morphism in the total category from compatible carrier and value maps. -/
def homMk {X Y : BilWFormCat R}
    (f : X.carrier →ₗ[R] Y.carrier) (α : X.value →ₗ[R] Y.value)
    (h : ∀ x y, α (X.pairing x y) = Y.pairing (f x) (f y)) : X ⟶ Y where
  base := ModuleCat.ofHom α
  fiber := by
    refine Quiver.Hom.op (CategoryOfElements.homMk _ _
      (op (ModuleCat.ofHom f)) ?_)
    dsimp [bilinearForms]
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => exact (h x y).symm
    | add x y hx hy => simp [hx, hy]

@[ext]
theorem hom_ext {X Y : BilWFormCat R} (f g : X ⟶ Y)
    (hValue : valueMap f = valueMap g)
    (hCarrier : carrierMap f = carrierMap g) : f = g := by
  cases f with
  | mk fBase fFiber =>
    cases g with
    | mk gBase gFiber =>
      dsimp [valueMap] at hValue
      subst gBase
      congr
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      exact congrArg ModuleCat.Hom.hom hCarrier

/-- The zero morphism in the total formed-module category. -/
def zeroHom (X Y : BilWFormCat R) : X ⟶ Y :=
  homMk 0 0 (by
    intro x y
    change 0 = Y.formed.bilinMap 0 0
    rw [map_zero])

instance (X Y : BilWFormCat R) : Zero (X ⟶ Y) :=
  ⟨zeroHom X Y⟩

@[simp]
theorem valueMap_zero (X Y : BilWFormCat R) : valueMap (0 : X ⟶ Y) = 0 :=
  rfl

@[simp]
theorem carrierMap_zero (X Y : BilWFormCat R) : carrierMap (0 : X ⟶ Y) = 0 :=
  rfl

@[simp]
theorem valueMap_comp {X Y Z : BilWFormCat R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    valueMap (f ≫ g) = valueMap f ≫ valueMap g :=
  rfl

@[simp]
theorem carrierMap_comp {X Y Z : BilWFormCat R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    carrierMap (f ≫ g) = carrierMap f ≫ carrierMap g :=
  rfl

instance : HasZeroMorphisms (BilWFormCat R) where
  comp_zero := by
    intro X Y f Z
    apply hom_ext
    · rw [valueMap_comp, valueMap_zero]
      simp
    · rw [carrierMap_comp, carrierMap_zero]
      simp
  zero_comp := by
    intro X Y Z f
    apply hom_ext
    · rw [valueMap_comp, valueMap_zero]
      simp
    · rw [carrierMap_comp, carrierMap_zero]
      simp

/-- Morphisms in the total category preserve forms through their value maps. -/
theorem map_pairing {X Y : BilWFormCat R} (f : X ⟶ Y)
    (x y : X.carrier) :
    (valueMap f).hom (X.pairing x y) =
      Y.pairing ((carrierMap f).hom x) ((carrierMap f).hom y) :=
  (BilinModuleCat.map_pairing f.fiber x y).symm

/-- Build a formed isomorphism from compatible carrier and value equivalences. -/
def isoMk {X Y : BilWFormCat R}
    (f : X.carrier ≃ₗ[R] Y.carrier)
    (α : X.value ≃ₗ[R] Y.value)
    (h : ∀ x y, α (X.pairing x y) = Y.pairing (f x) (f y)) :
    X ≅ Y := by
  have hinv : ∀ x y,
      α.symm (Y.pairing x y) = X.pairing (f.symm x) (f.symm y) := by
    intro x y
    apply α.injective
    change α (α.symm (Y.pairing x y)) =
      α (X.pairing (f.symm x) (f.symm y))
    rw [α.apply_symm_apply, h, f.apply_symm_apply, f.apply_symm_apply]
  refine ⟨homMk f.toLinearMap α.toLinearMap h,
    homMk f.symm.toLinearMap α.symm.toLinearMap hinv, ?_, ?_⟩
  · apply hom_ext
    · apply ModuleCat.hom_ext
      ext x
      exact α.symm_apply_apply x
    · apply ModuleCat.hom_ext
      ext x
      exact f.symm_apply_apply x
  · apply hom_ext
    · apply ModuleCat.hom_ext
      ext x
      exact α.apply_symm_apply x
    · apply ModuleCat.hom_ext
      ext x
      exact f.apply_symm_apply x

end BilWFormCat

/-- Include one fixed-value fiber into the total formed-module category. -/
abbrev fixedValueInclusion (W : ModuleCat.{u} R) :
    BilinModuleCat R W ⥤ BilWFormCat R :=
  Grothendieck.ι (valueFibers R) W

@[simp]
theorem fixedValueInclusion_value (W : ModuleCat.{u} R)
    (L : BilinModuleCat R W) :
    ((fixedValueInclusion R W).obj L).value = W :=
  rfl

@[simp]
theorem fixedValueInclusion_formed (W : ModuleCat.{u} R)
    (L : BilinModuleCat R W) :
    ((fixedValueInclusion R W).obj L).formed = L :=
  rfl

end LeanCategories.Modules.Bilinear.Valued

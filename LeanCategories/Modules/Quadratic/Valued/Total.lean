/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Quadratic.Valued.ChangeValue
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace LeanCategories.Modules.Quadratic.Valued

universe u

variable (R : Type u) [CommRing R]

/-- The functor of quadratic-module categories indexed by their value modules. -/
def quadraticValueFibers : ModuleCat.{u} R ⥤ Cat.{u, u + 1} where
  obj W := Cat.of (QuadModuleCat R W)
  map {W _} α := (changeValue R W α.hom).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The category of quadratic `R`-modules with a variable module of values. -/
abbrev QuadWFormCat := Grothendieck (quadraticValueFibers R)

namespace QuadWFormCat

variable {R}

/-- The value module of a quadratic formed module in the total category. -/
abbrev value (X : QuadWFormCat R) : ModuleCat R := X.base

/-- The fixed-value quadratic formed module underlying a total object. -/
abbrev formed (X : QuadWFormCat R) : QuadModuleCat R X.value := X.fiber

/-- The carrier module of a total quadratic formed module. -/
abbrev carrier (X : QuadWFormCat R) : ModuleCat R := X.formed.carrierObj

/-- The quadratic form of an object in the total category. -/
abbrev form (X : QuadWFormCat R) : QuadraticMap R (X.carrier : Type u) X.value :=
  X.formed.form

/-- The polarized bilinear form of a total quadratic formed module. -/
abbrev polarBilin (X : QuadWFormCat R) := X.formed.polarBilin

/-- The adjoint of the polarized form of a total quadratic formed module. -/
abbrev adjoint (X : QuadWFormCat R) := X.form.polarBilin

/-- The left radical of the polarized form of a total quadratic formed module. -/
abbrev leftRadical (X : QuadWFormCat R) := X.form.polarBilin.ker

/-- The right radical of the polarized form of a total quadratic formed module. -/
abbrev rightRadical (X : QuadWFormCat R) := X.form.polarBilin.flip.ker

/-- The radical of a total quadratic formed module. -/
abbrev radical (X : QuadWFormCat R) := X.form.radical

/-- Left nondegeneracy of the polarized form of a total quadratic formed module. -/
def IsLeftNondegenerate (X : QuadWFormCat R) : Prop :=
  X.formed.polarBilin.SeparatingLeft

/-- Right nondegeneracy of the polarized form of a total quadratic formed module. -/
def IsRightNondegenerate (X : QuadWFormCat R) : Prop :=
  X.formed.polarBilin.SeparatingRight

/-- Nondegeneracy of the quadratic map of a total formed module. -/
def IsNondegenerate (X : QuadWFormCat R) : Prop :=
  X.form.Nondegenerate

/-- The map between value modules underlying a total morphism. -/
abbrev valueMap {X Y : QuadWFormCat R} (f : X ⟶ Y) : X.value ⟶ Y.value :=
  f.base

/-- The map between carrier modules underlying a total morphism. -/
abbrev carrierMap {X Y : QuadWFormCat R} (f : X ⟶ Y) : X.carrier ⟶ Y.carrier :=
  ModuleCat.ofHom (QuadModuleCat.underlyingMap f.fiber)

/-- Build a total quadratic formed module from a carrier, value module, and quadratic form. -/
def of (M W : ModuleCat.{u} R)
    (q : QuadraticMap R (M : Type u) W) : QuadWFormCat R where
  base := W
  fiber := op ⟨op M, q⟩

/-- Build a total morphism from compatible carrier and value maps. -/
def homMk {X Y : QuadWFormCat R}
    (f : X.carrier →ₗ[R] Y.carrier) (α : X.value →ₗ[R] Y.value)
    (h : ∀ x, α (X.form x) = Y.form (f x)) : X ⟶ Y where
  base := ModuleCat.ofHom α
  fiber := by
    refine Quiver.Hom.op (CategoryOfElements.homMk _ _
      (op (ModuleCat.ofHom f)) ?_)
    dsimp [quadraticMaps]
    ext x
    exact (h x).symm

@[ext]
theorem hom_ext {X Y : QuadWFormCat R} (f g : X ⟶ Y)
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

@[simp]
theorem valueMap_comp {X Y Z : QuadWFormCat R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    valueMap (f ≫ g) = valueMap f ≫ valueMap g :=
  rfl

@[simp]
theorem carrierMap_comp {X Y Z : QuadWFormCat R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    carrierMap (f ≫ g) = carrierMap f ≫ carrierMap g :=
  rfl

/-- Total morphisms preserve quadratic forms through their value maps. -/
theorem map_form {X Y : QuadWFormCat R} (f : X ⟶ Y) (x : X.carrier) :
    (valueMap f).hom (X.form x) = Y.form ((carrierMap f).hom x) :=
  (QuadModuleCat.map_form f.fiber x).symm

/-- Build a total quadratic formed-module isomorphism. -/
def isoMk {X Y : QuadWFormCat R}
    (f : X.carrier ≃ₗ[R] Y.carrier)
    (α : X.value ≃ₗ[R] Y.value)
    (h : ∀ x, α (X.form x) = Y.form (f x)) : X ≅ Y := by
  have hinv : ∀ x, α.symm (Y.form x) = X.form (f.symm x) := by
    intro x
    apply α.injective
    change α (α.symm (Y.form x)) = α (X.form (f.symm x))
    rw [α.apply_symm_apply, h, f.apply_symm_apply]
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

end QuadWFormCat

/-- Include one fixed-value quadratic fiber into the total category. -/
abbrev fixedValueInclusion (W : ModuleCat.{u} R) :
    QuadModuleCat R W ⥤ QuadWFormCat R :=
  Grothendieck.ι (quadraticValueFibers R) W

/-- Project a total quadratic formed module to its value module. -/
def valueProjection : QuadWFormCat R ⥤ ModuleCat R where
  obj := QuadWFormCat.value
  map := fun f ↦ f.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Project a total quadratic formed module to its carrier module. -/
def carrierProjection : QuadWFormCat R ⥤ ModuleCat R where
  obj := QuadWFormCat.carrier
  map := QuadWFormCat.carrierMap
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem fixedValueInclusion_value (W : ModuleCat.{u} R)
    (Q : QuadModuleCat R W) :
    ((fixedValueInclusion R W).obj Q).value = W :=
  rfl

@[simp]
theorem fixedValueInclusion_formed (W : ModuleCat.{u} R)
    (Q : QuadModuleCat R W) :
    ((fixedValueInclusion R W).obj Q).formed = Q :=
  rfl

end LeanCategories.Modules.Quadratic.Valued

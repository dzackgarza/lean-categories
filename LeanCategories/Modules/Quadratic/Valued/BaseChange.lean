/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Quadratic.Valued.Total
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section

open CategoryTheory
open Opposite

namespace LeanCategories.Modules.Quadratic.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

section BaseChange

variable (S : Type u) [CommRing S] [Algebra R S]
variable [Invertible (2 : R)]

/-- Scalar extension of a quadratic form to the tensor-product carrier and value module. -/
def baseChangeForm (Q : QuadModuleCat R W) :
    QuadraticMap S (TensorProduct R S Q.carrier) (TensorProduct R S W) :=
  (QuadraticMap.sq (R := S)).tmul Q.form

/-- Scalar extension of one fixed-value quadratic module. -/
def baseChangeObject (Q : QuadModuleCat R W) :
    QuadModuleCat S (TensorProduct R S W) :=
  op ⟨op (ModuleCat.of S (TensorProduct R S Q.carrier)), baseChangeForm R W S Q⟩

/-- Scalar extension on the category of fixed-value quadratic modules. -/
def baseChangeQuadModule :
    QuadModuleCat R W ⥤ QuadModuleCat S (TensorProduct R S W) where
  obj := baseChangeObject R W S
  map {Q P} f := by
    refine QuadModuleCat.homMk (LinearMap.baseChange S (QuadModuleCat.underlyingMap f)) ?_
    have hq :
        (baseChangeForm R W S P).comp
            (LinearMap.baseChange S (QuadModuleCat.underlyingMap f)) =
          baseChangeForm R W S Q := by
      apply baseChange_ext
      intro x
      simp only [baseChangeForm, QuadraticMap.comp_apply, LinearMap.baseChange_tmul,
        QuadraticMap.tensorDistrib_tmul]
      rw [QuadModuleCat.map_form f]
    exact fun x => QuadraticMap.congr_fun hq x
  map_id Q := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_id
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    change LinearMap.baseChange S
        (QuadModuleCat.underlyingMap g ∘ₗ QuadModuleCat.underlyingMap f) =
      LinearMap.baseChange S (QuadModuleCat.underlyingMap g) ∘ₗ
        LinearMap.baseChange S (QuadModuleCat.underlyingMap f)
    rw [LinearMap.baseChange_comp]

/-- Scalar extension on the total category of variable-valued quadratic forms. -/
def baseChangeQuadWForm : QuadWFormCat R ⥤ QuadWFormCat S where
  obj X := by
    refine ⟨ModuleCat.of S (TensorProduct R S X.value), ?_⟩
    exact baseChangeObject R X.value S X.formed
  map {X Y} f := by
    refine QuadWFormCat.homMk
      (LinearMap.baseChange S (QuadWFormCat.carrierMap f).hom)
      (LinearMap.baseChange S (QuadWFormCat.valueMap f).hom) ?_
    have hq :
        (LinearMap.baseChange S (QuadWFormCat.valueMap f).hom).compQuadraticMap
            (baseChangeForm R X.value S X.formed) =
          (baseChangeForm R Y.value S Y.formed).comp
            (LinearMap.baseChange S (QuadWFormCat.carrierMap f).hom) := by
      apply baseChange_ext
      intro x
      change
        (LinearMap.baseChange S (QuadWFormCat.valueMap f).hom)
            ((baseChangeForm R X.value S X.formed) (1 ⊗ₜ[R] x)) =
          (baseChangeForm R Y.value S Y.formed)
            ((LinearMap.baseChange S (QuadWFormCat.carrierMap f).hom) (1 ⊗ₜ[R] x))
      simp only [baseChangeForm, LinearMap.baseChange_tmul,
        QuadraticMap.tensorDistrib_tmul, QuadWFormCat.map_form]
    exact fun x => QuadraticMap.congr_fun hq x
  map_id X := by
    apply QuadWFormCat.hom_ext
    · apply ModuleCat.hom_ext
      exact LinearMap.baseChange_id
    · apply ModuleCat.hom_ext
      exact LinearMap.baseChange_id
  map_comp f g := by
    apply QuadWFormCat.hom_ext
    · apply ModuleCat.hom_ext
      change LinearMap.baseChange S
          ((QuadWFormCat.valueMap g).hom ∘ₗ (QuadWFormCat.valueMap f).hom) =
        LinearMap.baseChange S (QuadWFormCat.valueMap g).hom ∘ₗ
          LinearMap.baseChange S (QuadWFormCat.valueMap f).hom
      rw [LinearMap.baseChange_comp]
    · apply ModuleCat.hom_ext
      change LinearMap.baseChange S
          ((QuadWFormCat.carrierMap g).hom ∘ₗ (QuadWFormCat.carrierMap f).hom) =
        LinearMap.baseChange S (QuadWFormCat.carrierMap g).hom ∘ₗ
          LinearMap.baseChange S (QuadWFormCat.carrierMap f).hom
      rw [LinearMap.baseChange_comp]

end BaseChange

end LeanCategories.Modules.Quadratic.Valued

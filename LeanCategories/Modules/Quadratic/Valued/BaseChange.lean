/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Quadratic.Valued.Total
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import LeanCategories.ForMathlib.QuadraticBaseChange
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

/-- Scalar extension of a quadratic form to the tensor-product carrier and value module:
`(s ⊗ m) ↦ s² ⊗ Q m`, over any commutative rings (`QuadraticMap.baseChange'`, no hypothesis on
`2`). -/
noncomputable def baseChangeForm (Q : QuadModuleCat R W) :
    QuadraticMap S (TensorProduct R S Q.carrier) (TensorProduct R S W) :=
  QuadraticMap.baseChange' S Q.form

/-- Scalar extension of one fixed-value quadratic module. -/
noncomputable def baseChangeObject (Q : QuadModuleCat R W) :
    QuadModuleCat S (TensorProduct R S W) :=
  op ⟨op (ModuleCat.of S (TensorProduct R S Q.carrier)), baseChangeForm R W S Q⟩

/-- Scalar extension on the category of fixed-value quadratic modules. -/
noncomputable def baseChangeQuadModule :
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
        QuadraticMap.baseChange'_tmul]
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
noncomputable def baseChangeQuadWForm : QuadWFormCat R ⥤ QuadWFormCat S where
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
        QuadraticMap.baseChange'_tmul, QuadWFormCat.map_form]
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

section IdentityComparison

/-- Scalar extension along the identity ring map changes no formed object. -/
noncomputable def baseChangeQuadWFormIdentityIsoObj
    (X : QuadWFormCat R) :
    (baseChangeQuadWForm R R).obj X ≅ X :=
  QuadWFormCat.isoMk (TensorProduct.lid R X.carrier)
    (TensorProduct.lid R X.value) (by
      have hq : (TensorProduct.lid R X.value).toLinearMap.compQuadraticMap
            (QuadraticMap.baseChange' R X.form) =
          X.form.comp (TensorProduct.lid R X.carrier).toLinearMap := by
        apply _root_.baseChange_ext
        intro x
        simp
      exact fun x => QuadraticMap.congr_fun hq x)

/-- Identity scalar extension is naturally isomorphic to the identity functor. -/
noncomputable def baseChangeQuadWFormIdentityIso :
    baseChangeQuadWForm R R ≅ 𝟭 (QuadWFormCat R) :=
  NatIso.ofComponents (baseChangeQuadWFormIdentityIsoObj R) (by
    intro X Y f
    apply QuadWFormCat.hom_ext
    · apply ModuleCat.hom_ext
      change (TensorProduct.lid R Y.value).toLinearMap.comp
          (LinearMap.baseChange R (QuadWFormCat.valueMap f).hom) =
        (QuadWFormCat.valueMap f).hom.comp
          (TensorProduct.lid R X.value).toLinearMap
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a x =>
        simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul]
        change a • (QuadWFormCat.valueMap f).hom x =
          (QuadWFormCat.valueMap f).hom (a • x)
        exact ((QuadWFormCat.valueMap f).hom.map_smul a x).symm
      | add x y hx hy => simp only [map_add, hx, hy]
    · apply ModuleCat.hom_ext
      change (TensorProduct.lid R Y.carrier).toLinearMap.comp
          (LinearMap.baseChange R (QuadWFormCat.carrierMap f).hom) =
        (QuadWFormCat.carrierMap f).hom.comp
          (TensorProduct.lid R X.carrier).toLinearMap
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a x =>
        simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul]
        change a • (QuadWFormCat.carrierMap f).hom x =
          (QuadWFormCat.carrierMap f).hom (a • x)
        exact ((QuadWFormCat.carrierMap f).hom.map_smul a x).symm
      | add x y hx hy => simp only [map_add, hx, hy])

end IdentityComparison

section CompositionComparison

variable (T : Type u) [CommRing T]
variable [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Direct and iterated scalar extension give isomorphic formed objects. -/
noncomputable def baseChangeQuadWFormCompositionIsoObj
    (X : QuadWFormCat R) :
    (baseChangeQuadWForm R T).obj X ≅
      (baseChangeQuadWForm S T).obj ((baseChangeQuadWForm R S).obj X) :=
  QuadWFormCat.isoMk
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T X.carrier).symm
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T X.value).symm (by
      have hq : LinearMap.compQuadraticMap
            (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T X.value).symm.toLinearMap
            (QuadraticMap.baseChange' T X.form) =
          (QuadraticMap.baseChange' T (QuadraticMap.baseChange' S X.form)).comp
            (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T X.carrier).symm.toLinearMap := by
        apply _root_.baseChange_ext
        intro x
        simp
      exact fun x => QuadraticMap.congr_fun hq x)

/-- Direct scalar extension equals iterated extension up to natural isomorphism. -/
noncomputable def baseChangeQuadWFormCompositionIso :
    baseChangeQuadWForm R T ≅
      baseChangeQuadWForm R S ⋙ baseChangeQuadWForm S T :=
  NatIso.ofComponents (baseChangeQuadWFormCompositionIsoObj R S T) (by
    intro X Y f
    apply QuadWFormCat.hom_ext
    · apply ModuleCat.hom_ext
      change (TensorProduct.AlgebraTensorModule.cancelBaseChange
          R S T T Y.value).symm.toLinearMap.comp
          (LinearMap.baseChange T (QuadWFormCat.valueMap f).hom) =
        (LinearMap.baseChange T
          (LinearMap.baseChange S (QuadWFormCat.valueMap f).hom)).comp
            (TensorProduct.AlgebraTensorModule.cancelBaseChange
              R S T T X.value).symm.toLinearMap
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a x =>
        simp only [LinearMap.comp_apply]
        change a ⊗ₜ[S] (1 ⊗ₜ[R] (QuadWFormCat.valueMap f).hom x) =
          a ⊗ₜ[S] (1 ⊗ₜ[R] (QuadWFormCat.valueMap f).hom x)
        rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    · apply ModuleCat.hom_ext
      change (TensorProduct.AlgebraTensorModule.cancelBaseChange
          R S T T Y.carrier).symm.toLinearMap.comp
          (LinearMap.baseChange T (QuadWFormCat.carrierMap f).hom) =
        (LinearMap.baseChange T
          (LinearMap.baseChange S (QuadWFormCat.carrierMap f).hom)).comp
            (TensorProduct.AlgebraTensorModule.cancelBaseChange
              R S T T X.carrier).symm.toLinearMap
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a x =>
        simp only [LinearMap.comp_apply]
        change a ⊗ₜ[S] (1 ⊗ₜ[R] (QuadWFormCat.carrierMap f).hom x) =
          a ⊗ₜ[S] (1 ⊗ₜ[R] (QuadWFormCat.carrierMap f).hom x)
        rfl
      | add x y hx hy => simp only [map_add, hx, hy])

end CompositionComparison

end BaseChange

end LeanCategories.Modules.Quadratic.Valued

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.BaseChange

@[expose] public section

/-!
# Coherence of base change of bilinear forms

The identity and composition isomorphisms of `baseChangeBilWForm` (`BaseChange.lean`)
satisfy the associativity and unit laws of a pseudofunctor. The statements and proofs
follow Mathlib's `ModuleCat.extendScalars_assoc'`, `extendScalars_id_comp` and
`extendScalars_comp_id`: each law is checked on pure tensors of the value and carrier
modules.
-/

open CategoryTheory TensorProduct

namespace LeanCategories.Lattices.Valued

universe u

open LeanCategories.Modules.Bilinear.Valued

section Components

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

@[simp]
theorem valueMap_baseChangeBilWForm_map {X Y : BilWFormCat R} (g : X ⟶ Y) :
    BilWFormCat.valueMap ((baseChangeBilWForm R S).map g) =
      ModuleCat.ofHom (LinearMap.baseChange S (BilWFormCat.valueMap g).hom) :=
  rfl

@[simp]
theorem carrierMap_baseChangeBilWForm_map {X Y : BilWFormCat R} (g : X ⟶ Y) :
    BilWFormCat.carrierMap ((baseChangeBilWForm R S).map g) =
      ModuleCat.ofHom (LinearMap.baseChange S (BilWFormCat.carrierMap g).hom) :=
  rfl

@[simp]
theorem valueMap_compositionIso_hom_app (X : BilWFormCat R) :
    BilWFormCat.valueMap ((baseChangeBilWFormCompositionIso R S T).hom.app X) =
      ModuleCat.ofHom
        (AlgebraTensorModule.cancelBaseChange R S T T X.value).symm.toLinearMap :=
  rfl

@[simp]
theorem carrierMap_compositionIso_hom_app (X : BilWFormCat R) :
    BilWFormCat.carrierMap ((baseChangeBilWFormCompositionIso R S T).hom.app X) =
      ModuleCat.ofHom
        (AlgebraTensorModule.cancelBaseChange R S T T X.carrier).symm.toLinearMap :=
  rfl

@[simp]
theorem valueMap_compositionIso_inv_app (X : BilWFormCat R) :
    BilWFormCat.valueMap ((baseChangeBilWFormCompositionIso R S T).inv.app X) =
      ModuleCat.ofHom
        (AlgebraTensorModule.cancelBaseChange R S T T X.value).toLinearMap :=
  rfl

@[simp]
theorem carrierMap_compositionIso_inv_app (X : BilWFormCat R) :
    BilWFormCat.carrierMap ((baseChangeBilWFormCompositionIso R S T).inv.app X) =
      ModuleCat.ofHom
        (AlgebraTensorModule.cancelBaseChange R S T T X.carrier).toLinearMap :=
  rfl

@[simp]
theorem valueMap_identityIso_hom_app (X : BilWFormCat R) :
    BilWFormCat.valueMap ((baseChangeBilWFormIdentityIso R).hom.app X) =
      ModuleCat.ofHom (TensorProduct.lid R X.value).toLinearMap :=
  rfl

@[simp]
theorem carrierMap_identityIso_hom_app (X : BilWFormCat R) :
    BilWFormCat.carrierMap ((baseChangeBilWFormIdentityIso R).hom.app X) =
      ModuleCat.ofHom (TensorProduct.lid R X.carrier).toLinearMap :=
  rfl

end Components

section Associativity

variable (R S T U : Type u) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
variable [Algebra R S] [Algebra S T] [Algebra T U] [Algebra R T] [Algebra S U] [Algebra R U]
variable [IsScalarTower R S T] [IsScalarTower R T U] [IsScalarTower S T U]
  [IsScalarTower R S U]

/-- On the underlying modules, the associativity composite of cancellation isomorphisms
`U ⊗[R] W → U ⊗[T] (T ⊗[R] W) → U ⊗[T] (T ⊗[S] (S ⊗[R] W)) → U ⊗[S] (S ⊗[R] W) → U ⊗[R] W`
is the identity. -/
theorem cancelBaseChange_assoc (W : Type u) [AddCommGroup W] [Module R W] :
    (AlgebraTensorModule.cancelBaseChange R S U U W).toLinearMap ∘ₗ
      (AlgebraTensorModule.cancelBaseChange S T U U (S ⊗[R] W)).toLinearMap ∘ₗ
      LinearMap.baseChange U
        (AlgebraTensorModule.cancelBaseChange R S T T W).symm.toLinearMap ∘ₗ
      (AlgebraTensorModule.cancelBaseChange R T U U W).symm.toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul u w =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
      AlgebraTensorModule.cancelBaseChange_tmul, one_smul, LinearMap.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency.types false in
/-- The associativity law of the composition isomorphisms of base change. -/
theorem baseChangeBilWForm_assoc :
    (baseChangeBilWFormCompositionIso R T U).hom ≫
      Functor.whiskerRight (baseChangeBilWFormCompositionIso R S T).hom
        (baseChangeBilWForm T U) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (baseChangeBilWForm R S)
        (baseChangeBilWFormCompositionIso S T U).inv ≫
      (baseChangeBilWFormCompositionIso R S U).inv = 𝟙 _ := by
  ext X : 2
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, NatTrans.id_app, Category.id_comp]
  apply BilWFormCat.hom_ext
  · exact ModuleCat.hom_ext (cancelBaseChange_assoc R S T U X.value)
  · exact ModuleCat.hom_ext (cancelBaseChange_assoc R S T U X.carrier)

end Associativity

section Unitors

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Left unitality on underlying modules: `S ⊗[R] W → S ⊗[R] (R ⊗[R] W) → S ⊗[R] W` is the
identity. -/
theorem cancelBaseChange_id_left (W : Type u) [AddCommGroup W] [Module R W] :
    LinearMap.baseChange S (TensorProduct.lid R W).toLinearMap ∘ₗ
      (AlgebraTensorModule.cancelBaseChange R R S S W).symm.toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s w =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
      TensorProduct.lid_tmul, one_smul, LinearMap.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Right unitality on underlying modules: `S ⊗[R] W → S ⊗[S] (S ⊗[R] W) → S ⊗[R] W` is the
identity. -/
theorem cancelBaseChange_id_right (W : Type u) [AddCommGroup W] [Module R W] :
    (TensorProduct.lid S (S ⊗[R] W)).toLinearMap ∘ₗ
      (AlgebraTensorModule.cancelBaseChange R S S S W).symm.toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s w =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      AlgebraTensorModule.cancelBaseChange_symm_tmul, TensorProduct.lid_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one, LinearMap.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The left unit law of base change. -/
theorem baseChangeBilWForm_id_comp :
    (baseChangeBilWFormCompositionIso R R S).hom ≫
      Functor.whiskerRight (baseChangeBilWFormIdentityIso R).hom (baseChangeBilWForm R S) ≫
      (Functor.leftUnitor _).hom = 𝟙 _ := by
  ext X : 2
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    NatTrans.id_app]
  apply BilWFormCat.hom_ext
  · exact ModuleCat.hom_ext (cancelBaseChange_id_left R S X.value)
  · exact ModuleCat.hom_ext (cancelBaseChange_id_left R S X.carrier)

/-- The right unit law of base change. -/
theorem baseChangeBilWForm_comp_id :
    (baseChangeBilWFormCompositionIso R S S).hom ≫
      Functor.whiskerLeft (baseChangeBilWForm R S) (baseChangeBilWFormIdentityIso S).hom ≫
      (Functor.rightUnitor _).hom = 𝟙 _ := by
  ext X : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    NatTrans.id_app]
  apply BilWFormCat.hom_ext
  · exact ModuleCat.hom_ext (cancelBaseChange_id_right R S X.value)
  · exact ModuleCat.hom_ext (cancelBaseChange_id_right R S X.carrier)

end Unitors

end LeanCategories.Lattices.Valued

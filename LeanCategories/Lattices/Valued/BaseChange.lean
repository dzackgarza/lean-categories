/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.ChangeValue

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

section BaseChange

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Scalar extension of the form. -/
def baseChangeForm (L : BilinModuleCat R W) :
    TensorProduct S (TensorProduct R S L.carrier) (TensorProduct R S L.carrier) →ₗ[S]
      TensorProduct R S W :=
  (TensorProduct.lift.equiv (.id S) (TensorProduct R S L.carrier)
    (TensorProduct R S L.carrier) (TensorProduct R S W))
      (LinearMap.BilinMap.baseChange S L.bilinMap)

/-- Scalar extension of a bilinear module. -/
def baseChangeObject (L : BilinModuleCat R W) : BilinModuleCat S (TensorProduct R S W) :=
  op ⟨op (ModuleCat.of S (TensorProduct R S L.carrier)), baseChangeForm R W S L⟩

/-- Scalar extension on the category of bilinear modules. -/
def baseChangeBilin : BilinModuleCat R W ⥤ BilinModuleCat S (TensorProduct R S W) where
  obj := baseChangeObject R W S
  map {L M} f := by
    refine Quiver.Hom.op (CategoryOfElements.homMk _ _
      (op (ModuleCat.ofHom (LinearMap.baseChange S (BilinModuleCat.underlyingMap f)))) ?_)
    dsimp [bilinearForms]
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul b y =>
          change (a * b) ⊗ₜ[R] M.pairing (BilinModuleCat.underlyingMap f x)
            (BilinModuleCat.underlyingMap f y) = (a * b) ⊗ₜ[R] L.pairing x y
          rw [BilinModuleCat.map_pairing f]
        | add y₁ y₂ hy₁ hy₂ =>
          rw [TensorProduct.tmul_add, map_add, map_add, hy₁, hy₂]
      | add x₁ x₂ hx₁ hx₂ =>
        rw [TensorProduct.add_tmul, map_add, map_add, hx₁, hx₂]
    | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]
  map_id L := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (LinearMap.baseChange S (LinearMap.id)) z = z
    rw [LinearMap.baseChange_id]
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (LinearMap.baseChange S
      (BilinModuleCat.underlyingMap g ∘ₗ BilinModuleCat.underlyingMap f)) z =
        (LinearMap.baseChange S (BilinModuleCat.underlyingMap g) ∘ₗ
          LinearMap.baseChange S (BilinModuleCat.underlyingMap f)) z
    rw [LinearMap.baseChange_comp]

/-- Scalar extension on the total category of variable-valued forms. -/
def baseChangeBilWForm : BilWFormCat R ⥤ BilWFormCat S where
  obj X := by
    refine ⟨ModuleCat.of S (TensorProduct R S X.value), ?_⟩
    exact baseChangeObject R X.value S X.formed
  map {X Y} f := by
    refine BilWFormCat.homMk
      (LinearMap.baseChange S (BilWFormCat.carrierMap f).hom)
      (LinearMap.baseChange S (BilWFormCat.valueMap f).hom) ?_
    intro x y
    change (LinearMap.baseChange S (BilWFormCat.valueMap f).hom)
        ((LinearMap.BilinMap.baseChange S X.formed.bilinMap) x y) =
      (LinearMap.BilinMap.baseChange S Y.formed.bilinMap)
        ((LinearMap.baseChange S (BilWFormCat.carrierMap f).hom) x)
        ((LinearMap.baseChange S (BilWFormCat.carrierMap f).hom) y)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b y =>
        change (a * b) ⊗ₜ[R]
            (BilWFormCat.valueMap f).hom (X.pairing x y) =
          (a * b) ⊗ₜ[R] Y.pairing
            ((BilWFormCat.carrierMap f).hom x)
            ((BilWFormCat.carrierMap f).hom y)
        rw [BilWFormCat.map_pairing]
      | add y₁ y₂ hy₁ hy₂ => simp [hy₁, hy₂]
    | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂]
  map_id X := by
    apply BilWFormCat.hom_ext
    · apply ModuleCat.hom_ext
      exact LinearMap.baseChange_id
    · apply ModuleCat.hom_ext
      exact LinearMap.baseChange_id
  map_comp f g := by
    apply BilWFormCat.hom_ext
    · apply ModuleCat.hom_ext
      exact LinearMap.baseChange_comp (A := S)
        (f := (BilWFormCat.valueMap f).hom) (BilWFormCat.valueMap g).hom
    · apply ModuleCat.hom_ext
      exact LinearMap.baseChange_comp (A := S)
        (f := (BilWFormCat.carrierMap f).hom) (BilWFormCat.carrierMap g).hom

/-- Scalar extension on the total category of symmetric variable-valued forms. -/
def baseChangeSymBilWForm : SymBilWFormCat R ⥤ SymBilWFormCat S where
  obj X := by
    refine ⟨(baseChangeBilWForm R S).obj X.obj, ?_⟩
    exact LinearMap.BilinMap.baseChange_isSymm X.property
  map f := ObjectProperty.homMk ((baseChangeBilWForm R S).map f.hom)
  map_id X := by
    apply ObjectProperty.hom_ext
    exact (baseChangeBilWForm R S).map_id X.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (baseChangeBilWForm R S).map_comp f.hom g.hom

/-- Scalar extension preserves finite projective symmetric lattices. -/
def baseChange : LatticeCat R W ⥤ LatticeCat S (TensorProduct R S W) where
  obj L := by
    letI : Module.Finite R L.obj.carrier := L.property.1
    letI : Module.Projective R L.obj.carrier := L.property.2.1
    refine ⟨baseChangeObject R W S L.obj, ?_⟩
    change Module.Finite S (TensorProduct R S L.obj.carrier) ∧
      Module.Projective S (TensorProduct R S L.obj.carrier) ∧
        ∀ x y, (LinearMap.BilinMap.baseChange S L.obj.bilinMap) x y =
          (LinearMap.BilinMap.baseChange S L.obj.bilinMap) y x
    exact ⟨inferInstance, inferInstance,
      LinearMap.BilinMap.baseChange_isSymm L.property.2.2⟩
  map f := ObjectProperty.homMk ((baseChangeBilin R W S).map f.hom)
  map_id L := by
    apply ObjectProperty.hom_ext
    exact (baseChangeBilin R W S).map_id L.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (baseChangeBilin R W S).map_comp f.hom g.hom

end BaseChange

/-- Scalar extension of an integral lattice along `R → S`. -/
noncomputable def baseChangeIntegral (S : Type u) [CommRing S] [Algebra R S] :
    IntegralLatticeCat R ⥤ IntegralLatticeCat S where
  obj L :=
    (changeValue S (TensorProduct R S R)
      (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap).obj
        ((baseChange R R S).obj L)
  map f :=
    (changeValue S (TensorProduct R S R)
      (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap).map
        ((baseChange R R S).map f)
  map_id L := by simp
  map_comp f g := by simp

end LeanCategories.Lattices.Valued


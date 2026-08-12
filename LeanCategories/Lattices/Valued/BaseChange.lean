/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Arithmetic
public import LeanCategories.Lattices.Valued.ChangeValue
public import LeanCategories.Modules.Bilinear.Valued.OrthogonalGroup
public import LeanCategories.Modules.Bilinear.Valued.Properties
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u v

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

section BaseChange

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Flat scalar extension preserves exact sequences of linear maps. -/
theorem baseChange_exact [Module.Flat R S]
    {M N P : Type v}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (h : Function.Exact f g) :
    Function.Exact (LinearMap.baseChange S f)
      (LinearMap.baseChange S g) := by
  simpa only [LinearMap.baseChange_eq_ltensor] using
    Module.Flat.lTensor_exact S h

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

section IdentityComparison

/-- Scalar extension along the identity ring map changes no formed object. -/
noncomputable def baseChangeBilWFormIdentityIsoObj
    (X : BilWFormCat R) :
    (baseChangeBilWForm R R).obj X ≅ X :=
  BilWFormCat.isoMk (TensorProduct.lid R X.carrier)
    (TensorProduct.lid R X.value) (by
      intro x y
      change (TensorProduct.lid R X.value)
          (LinearMap.BilinMap.baseChange R X.formed.bilinMap x y) =
        X.formed.bilinMap ((TensorProduct.lid R X.carrier) x)
          ((TensorProduct.lid R X.carrier) y)
      induction x using TensorProduct.induction_on with
      | zero => simp only [LinearMap.zero_apply, map_zero]
      | tmul a x =>
        induction y using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul b y =>
          simp only [LinearMap.BilinMap.baseChange_tmul]
          rw [TensorProduct.lid_tmul, TensorProduct.lid_tmul,
            TensorProduct.lid_tmul]
          simp only [map_smul, LinearMap.smul_apply]
          rw [smul_smul, mul_comm]
        | add y₁ y₂ hy₁ hy₂ =>
          simp only [map_add, hy₁, hy₂]
      | add x₁ x₂ hx₁ hx₂ =>
        simp only [map_add, LinearMap.add_apply, hx₁, hx₂])

/-- Identity scalar extension is naturally isomorphic to the identity functor. -/
noncomputable def baseChangeBilWFormIdentityIso :
    baseChangeBilWForm R R ≅ 𝟭 (BilWFormCat R) :=
  NatIso.ofComponents (baseChangeBilWFormIdentityIsoObj R) (by
    intro X Y f
    apply BilWFormCat.hom_ext
    · apply ModuleCat.hom_ext
      change (TensorProduct.lid R Y.value).toLinearMap.comp
          (LinearMap.baseChange R (BilWFormCat.valueMap f).hom) =
        (BilWFormCat.valueMap f).hom.comp
          (TensorProduct.lid R X.value).toLinearMap
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a x =>
        simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul]
        change a • (BilWFormCat.valueMap f).hom x =
          (BilWFormCat.valueMap f).hom (a • x)
        exact ((BilWFormCat.valueMap f).hom.map_smul a x).symm
      | add x y hx hy => simp only [map_add, hx, hy]
    · apply ModuleCat.hom_ext
      change (TensorProduct.lid R Y.carrier).toLinearMap.comp
          (LinearMap.baseChange R (BilWFormCat.carrierMap f).hom) =
        (BilWFormCat.carrierMap f).hom.comp
          (TensorProduct.lid R X.carrier).toLinearMap
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a x =>
        simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul]
        change a • (BilWFormCat.carrierMap f).hom x =
          (BilWFormCat.carrierMap f).hom (a • x)
        exact ((BilWFormCat.carrierMap f).hom.map_smul a x).symm
      | add x y hx hy => simp only [map_add, hx, hy])

end IdentityComparison

section CompositionComparison

variable (T : Type u) [CommRing T]
variable [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Direct and iterated scalar extension give isomorphic formed objects. -/
noncomputable def baseChangeBilWFormCompositionIsoObj
    (X : BilWFormCat R) :
    (baseChangeBilWForm R T).obj X ≅
      (baseChangeBilWForm S T).obj ((baseChangeBilWForm R S).obj X) :=
  BilWFormCat.isoMk
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T X.carrier).symm
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T X.value).symm (by
      intro x y
      change (TensorProduct.AlgebraTensorModule.cancelBaseChange
          R S T T X.value).symm
          (LinearMap.BilinMap.baseChange T X.formed.bilinMap x y) =
        LinearMap.BilinMap.baseChange T
          (LinearMap.BilinMap.baseChange S X.formed.bilinMap)
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange
            R S T T X.carrier).symm x)
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange
            R S T T X.carrier).symm y)
      induction x using TensorProduct.induction_on with
      | zero => simp only [LinearMap.zero_apply, map_zero]
      | tmul a x =>
        induction y using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul b y => simp only [LinearMap.BilinMap.baseChange_tmul,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
            one_mul]
        | add y₁ y₂ hy₁ hy₂ =>
          simp only [map_add, hy₁, hy₂]
      | add x₁ x₂ hx₁ hx₂ =>
        simp only [map_add, LinearMap.add_apply, hx₁, hx₂])

/-- Direct scalar extension equals iterated extension up to natural isomorphism. -/
noncomputable def baseChangeBilWFormCompositionIso :
    baseChangeBilWForm R T ≅
      baseChangeBilWForm R S ⋙ baseChangeBilWForm S T :=
  NatIso.ofComponents (baseChangeBilWFormCompositionIsoObj R S T) (by
    intro X Y f
    apply BilWFormCat.hom_ext
    · apply ModuleCat.hom_ext
      change (TensorProduct.AlgebraTensorModule.cancelBaseChange
          R S T T Y.value).symm.toLinearMap.comp
          (LinearMap.baseChange T (BilWFormCat.valueMap f).hom) =
        (LinearMap.baseChange T
          (LinearMap.baseChange S (BilWFormCat.valueMap f).hom)).comp
            (TensorProduct.AlgebraTensorModule.cancelBaseChange
              R S T T X.value).symm.toLinearMap
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a x =>
        simp only [LinearMap.comp_apply]
        change a ⊗ₜ[S] (1 ⊗ₜ[R] (BilWFormCat.valueMap f).hom x) =
          a ⊗ₜ[S] (1 ⊗ₜ[R] (BilWFormCat.valueMap f).hom x)
        rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    · apply ModuleCat.hom_ext
      change (TensorProduct.AlgebraTensorModule.cancelBaseChange
          R S T T Y.carrier).symm.toLinearMap.comp
          (LinearMap.baseChange T (BilWFormCat.carrierMap f).hom) =
        (LinearMap.baseChange T
          (LinearMap.baseChange S (BilWFormCat.carrierMap f).hom)).comp
            (TensorProduct.AlgebraTensorModule.cancelBaseChange
              R S T T X.carrier).symm.toLinearMap
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a x =>
        simp only [LinearMap.comp_apply]
        change a ⊗ₜ[S] (1 ⊗ₜ[R] (BilWFormCat.carrierMap f).hom x) =
          a ⊗ₜ[S] (1 ⊗ₜ[R] (BilWFormCat.carrierMap f).hom x)
        rfl
      | add x y hx hy => simp only [map_add, hx, hy])

end CompositionComparison

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

/-- Scalar extension preserves projective symmetric lattices. -/
def baseChange : LatticeCat R W ⥤ LatticeCat S (TensorProduct R S W) where
  obj L := by
    letI : Module.Projective R L.obj.carrier := L.property.1
    refine ⟨baseChangeObject R W S L.obj, ?_⟩
    change Module.Projective S (TensorProduct R S L.obj.carrier) ∧
        ∀ x y, (LinearMap.BilinMap.baseChange S L.obj.bilinMap) x y =
          (LinearMap.BilinMap.baseChange S L.obj.bilinMap) y x
    exact ⟨inferInstance, LinearMap.BilinMap.baseChange_isSymm L.property.2⟩
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

@[simp]
theorem baseChangeIntegral_pairing_tmul
    (S : Type u) [CommRing S] [Algebra R S]
    (L : IntegralLatticeCat R) (a b : S) (x y : L.obj.carrier) :
    ((baseChangeIntegral R S).obj L).obj.pairing
        (a ⊗ₜ[R] x) (b ⊗ₜ[R] y) =
      (a * b) * algebraMap R S (L.obj.pairing x y) := by
  change (TensorProduct.AlgebraTensorModule.rid R S S)
      ((a * b) ⊗ₜ[R] L.obj.pairing x y) = _
  simp [Algebra.smul_def, mul_comm]

/-- The bilinear map underlying integral scalar extension, on its explicit tensor carrier. -/
def baseChangeIntegralBilinMap
    (S : Type u) [CommRing S] [Algebra R S]
    (L : IntegralLatticeCat R) :
    LinearMap.BilinMap S (TensorProduct R S L.obj.carrier) S :=
  (LinearMap.BilinMap.baseChange S L.obj.bilinMap).compr₂
    (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap

@[simp]
theorem baseChangeIntegralBilinMap_tmul
    (S : Type u) [CommRing S] [Algebra R S]
    (L : IntegralLatticeCat R) (a b : S) (x y : L.obj.carrier) :
    baseChangeIntegralBilinMap R S L (a ⊗ₜ[R] x) (b ⊗ₜ[R] y) =
      (a * b) * algebraMap R S (L.obj.pairing x y) := by
  simp [baseChangeIntegralBilinMap, LinearMap.BilinMap.baseChange_tmul,
    Algebra.smul_def, mul_comm]

/-- The explicit scalar-extension bilinear map equals the form carried by the
scalar-extension object. -/
theorem baseChangeIntegralBilinMap_apply
    (S : Type u) [CommRing S] [Algebra R S]
    (L : IntegralLatticeCat R)
    (x y : TensorProduct R S L.obj.carrier) :
    baseChangeIntegralBilinMap R S L x y =
      ((baseChangeIntegral R S).obj L).obj.pairing x y :=
  rfl

/-- Scalar extension of finite projective integral lattices. -/
noncomputable def baseChangeFiniteIntegral
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    FiniteProjectiveLatticeCat R R ⥤ FiniteProjectiveLatticeCat S S where
  obj L := by
    letI : Module.Finite R L.obj.obj.carrier := L.property
    refine ⟨(baseChangeIntegral R S).obj L.obj, ?_⟩
    change Module.Finite S (TensorProduct R S L.obj.obj.carrier)
    infer_instance
  map f := ObjectProperty.homMk ((baseChangeIntegral R S).map f.hom)
  map_id L := by
    apply ObjectProperty.hom_ext
    exact (baseChangeIntegral R S).map_id L.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (baseChangeIntegral R S).map_comp f.hom g.hom

/-- Scalar extension induces a homomorphism between orthogonal groups. -/
noncomputable def orthogonalGroupBaseChangeHom
    (S : Type u) [CommRing S] [Algebra R S]
    (L : IntegralLatticeCat R) :
    BilinModuleCat.OrthogonalGroup L.obj →*
      BilinModuleCat.OrthogonalGroup ((baseChangeIntegral R S).obj L).obj where
  toFun g := ⟨g.1.baseChange R S L.obj.carrier L.obj.carrier, by
    intro x y
    change TensorProduct R S L.obj.carrier at x y
    change baseChangeIntegralBilinMap R S L
        (g.1.baseChange R S L.obj.carrier L.obj.carrier x)
        (g.1.baseChange R S L.obj.carrier L.obj.carrier y) =
      baseChangeIntegralBilinMap R S L x y
    induction x using TensorProduct.induction_on with
    | zero => simp [baseChangeIntegralBilinMap]
    | tmul a x =>
        induction y using TensorProduct.induction_on with
        | zero => simp [baseChangeIntegralBilinMap]
        | tmul b y =>
            simp only [LinearEquiv.baseChange_tmul, baseChangeIntegralBilinMap_tmul]
            rw [g.property]
        | add y₁ y₂ hy₁ hy₂ =>
            simp only [map_add]
            rw [hy₁, hy₂]
    | add x₁ x₂ hx₁ hx₂ =>
        simp only [map_add, LinearMap.add_apply]
        rw [hx₁, hx₂]⟩
  map_one' := by
    apply Subtype.ext
    change (1 : L.obj.carrier ≃ₗ[R] L.obj.carrier).baseChange R S = 1
    exact LinearEquiv.baseChange_one (R := R) (A := S) L.obj.carrier
  map_mul' g h := by
    apply Subtype.ext
    change (g.1 * h.1).baseChange R S = g.1.baseChange R S * h.1.baseChange R S
    exact LinearEquiv.baseChange_mul (R := R) (A := S) (e := g.1) (f := h.1)

end LeanCategories.Lattices.Valued

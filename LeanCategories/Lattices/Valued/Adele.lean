/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.IntegralAdeleRing
public import LeanCategories.Lattices.Valued.BaseChange
public import LeanCategories.Lattices.Valued.OrthogonalGroup

/-!
# Adelic scalar extension of integral lattices

Adelization is scalar extension to the ring adele ring. The existing base-change functor transports
the carrier, value module, and bilinear form together.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open IsDedekindDomain NumberField
open LeanCategories.Modules.Bilinear.Valued
open scoped NumberField

namespace LeanCategories.Lattices.Valued

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- Scalar extension of integral lattices from `𝓞 K` to its ring adele ring. -/
def ringAdeleBaseChange :
    IntegralLatticeCat (𝓞 K) ⥤ IntegralLatticeCat (RingAdeleRing K) :=
  baseChangeIntegral (𝓞 K) (RingAdeleRing K)

/-- Scalar extension of finite projective lattices to the ring adele ring. -/
def finiteRingAdeleBaseChange :
    FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K) ⥤
      FiniteProjectiveLatticeCat (RingAdeleRing K) (RingAdeleRing K) :=
  baseChangeFiniteIntegral (𝓞 K) (RingAdeleRing K)

/-- Scalar extension of finite projective lattices to the integral finite adele ring. -/
def finiteIntegralAdeleBaseChange :
    FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K) ⥤
      FiniteProjectiveLatticeCat
        (FiniteIntegralAdeleRing (𝓞 K) K) (FiniteIntegralAdeleRing (𝓞 K) K) :=
  baseChangeFiniteIntegral (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K)

/-- The finite local scalar extensions of a finite projective lattice. -/
abbrev FiniteAdeleModuleProduct
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  FiniteIntegralAdeleRing.ModuleProduct (𝓞 K) K L.obj.obj.carrier

/-- The product of the local scalar extensions, with the scalar ring in the first tensor factor. -/
abbrev FiniteAdeleLocalModuleProduct
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  (v : HeightOneSpectrum (𝓞 K)) →
    TensorProduct (𝓞 K) (v.adicCompletionIntegers K) L.obj.obj.carrier

/-- The product ring acts on the product of local scalar extensions coordinatewise. -/
noncomputable instance finiteAdeleLocalModuleProductModule
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Module (FiniteIntegralAdeleRing (𝓞 K) K) (FiniteAdeleLocalModuleProduct K L) := by
  letI (v : HeightOneSpectrum (𝓞 K)) :
      Module (FiniteIntegralAdeleRing (𝓞 K) K)
        (TensorProduct (𝓞 K) (v.adicCompletionIntegers K) L.obj.obj.carrier) :=
    Module.compHom _ (Pi.evalRingHom
      (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletionIntegers K) v)
  infer_instance

/-- The finite part of adelic scalar extension is the product of all completed local scalar
extensions. -/
def finiteAdeleCarrierEquiv
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier ≃ₗ[𝓞 K]
      FiniteAdeleModuleProduct K L := by
  letI : Module.Finite (𝓞 K) L.obj.obj.carrier := L.property
  letI : Module.Projective (𝓞 K) L.obj.obj.carrier := L.obj.property.1
  exact (TensorProduct.comm (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K)
    L.obj.obj.carrier).trans
      (FiniteIntegralAdeleRing.tensorProductEquivModuleProduct
        (𝓞 K) K L.obj.obj.carrier)

@[simp]
theorem finiteAdeleCarrierEquiv_tmul
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K))
    (a : FiniteIntegralAdeleRing (𝓞 K) K) (x : L.obj.obj.carrier) :
    finiteAdeleCarrierEquiv K L (a ⊗ₜ[𝓞 K] x) =
      fun v ↦ x ⊗ₜ[𝓞 K] a v := by
  letI : Module.Finite (𝓞 K) L.obj.obj.carrier := L.property
  letI : Module.Projective (𝓞 K) L.obj.obj.carrier := L.obj.property.1
  change FiniteIntegralAdeleRing.tensorProductEquivModuleProduct
    (𝓞 K) K L.obj.obj.carrier
      ((TensorProduct.comm (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K)
        L.obj.obj.carrier) (a ⊗ₜ[𝓞 K] x)) = _
  rw [TensorProduct.comm_tmul,
    FiniteIntegralAdeleRing.tensorProductEquivModuleProduct_tmul]

/-- The finite adelic carrier as the product of the carriers obtained by local scalar extension. -/
def finiteAdeleLocalCarrierEquiv
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier ≃ₗ[𝓞 K]
      FiniteAdeleLocalModuleProduct K L :=
  (finiteAdeleCarrierEquiv K L).trans <|
    LinearEquiv.piCongrRight fun v ↦
      TensorProduct.comm (𝓞 K) L.obj.obj.carrier (v.adicCompletionIntegers K)

@[simp]
theorem finiteAdeleLocalCarrierEquiv_tmul
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K))
    (a : FiniteIntegralAdeleRing (𝓞 K) K) (x : L.obj.obj.carrier) :
    finiteAdeleLocalCarrierEquiv K L (a ⊗ₜ[𝓞 K] x) =
      fun v ↦ a v ⊗ₜ[𝓞 K] x := by
  ext v
  simp [finiteAdeleLocalCarrierEquiv, finiteAdeleCarrierEquiv_tmul]

/-- The local-carrier presentation is linear over the integral finite adele ring. -/
def finiteAdeleLocalCarrierAlgEquiv
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier
      ≃ₗ[FiniteIntegralAdeleRing (𝓞 K) K] FiniteAdeleLocalModuleProduct K L :=
  LinearEquiv.ofBijective
    { toFun := finiteAdeleLocalCarrierEquiv K L
      map_add' := map_add (finiteAdeleLocalCarrierEquiv K L)
      map_smul' := by
        intro a x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b x =>
            ext v
            change (a v * b v) ⊗ₜ[𝓞 K] x =
              a v • (b v ⊗ₜ[𝓞 K] x)
            rw [TensorProduct.smul_tmul']
            rfl
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
    (finiteAdeleLocalCarrierEquiv K L).bijective

@[simp]
theorem finiteAdeleLocalCarrierAlgEquiv_tmul
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K))
    (a : FiniteIntegralAdeleRing (𝓞 K) K) (x : L.obj.obj.carrier) :
    finiteAdeleLocalCarrierAlgEquiv K L (a ⊗ₜ[𝓞 K] x) =
      fun v ↦ a v ⊗ₜ[𝓞 K] x :=
  finiteAdeleLocalCarrierEquiv_tmul K L a x

/-- On pure tensors, each coordinate of the finite adelic form is the corresponding local
scalar-extension form. -/
theorem finiteIntegralAdeleBaseChange_pairing_tmul_apply
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K))
    (a b : FiniteIntegralAdeleRing (𝓞 K) K)
    (x y : L.obj.obj.carrier)
    (v : HeightOneSpectrum (𝓞 K)) :
    ((baseChangeIntegral (𝓞 K)
      (FiniteIntegralAdeleRing (𝓞 K) K)).obj L.obj).obj.pairing
        (a ⊗ₜ[𝓞 K] x) (b ⊗ₜ[𝓞 K] y) v =
      ((baseChangeIntegral (𝓞 K) (v.adicCompletionIntegers K)).obj L.obj).obj.pairing
        (a v ⊗ₜ[𝓞 K] x) (b v ⊗ₜ[𝓞 K] y) := by
  calc
    _ = ((a * b) * algebraMap (𝓞 K)
        (FiniteIntegralAdeleRing (𝓞 K) K) (L.obj.obj.pairing x y)) v :=
      congrArg (fun z : FiniteIntegralAdeleRing (𝓞 K) K ↦ z v)
        (baseChangeIntegral_pairing_tmul (𝓞 K)
          (FiniteIntegralAdeleRing (𝓞 K) K) L.obj a b x y)
    _ = (a v * b v) * algebraMap (𝓞 K)
        (v.adicCompletionIntegers K) (L.obj.obj.pairing x y) := rfl
    _ = _ := (baseChangeIntegral_pairing_tmul (𝓞 K)
      (v.adicCompletionIntegers K) L.obj (a v) (b v) x y).symm

/-- The finite adelic form as an `𝓞 K`-bilinear map on its explicit tensor carrier. -/
def finiteIntegralAdelePairing
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier →ₗ[𝓞 K]
      TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier →ₗ[𝓞 K]
        FiniteIntegralAdeleRing (𝓞 K) K :=
  (baseChangeIntegralBilinMap (𝓞 K)
    (FiniteIntegralAdeleRing (𝓞 K) K) L.obj).restrictScalars₁₂ (𝓞 K) (𝓞 K)

/-- The product of all local scalar-extension forms. -/
def finiteAdeleLocalPairing
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier →ₗ[𝓞 K]
      TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier →ₗ[𝓞 K]
        FiniteIntegralAdeleRing (𝓞 K) K :=
  LinearMap.mk₂ (𝓞 K)
    (fun x y v ↦ baseChangeIntegralBilinMap (𝓞 K)
      (v.adicCompletionIntegers K) L.obj
        (finiteAdeleLocalCarrierEquiv K L x v)
        (finiteAdeleLocalCarrierEquiv K L y v))
    (by intro x₁ x₂ y; funext v; simp)
    (by intro r x y; funext v; simp)
    (by intro x y₁ y₂; funext v; simp)
    (by intro r x y; funext v; simp)

/-- The finite adelic form is the product of its local scalar-extension forms. -/
theorem finiteIntegralAdelePairing_eq_localPairing
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    finiteIntegralAdelePairing K L = finiteAdeleLocalPairing K L := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      apply LinearMap.ext
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b y =>
          funext v
          simp [finiteIntegralAdelePairing, finiteAdeleLocalPairing]
      | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]

/-- Every pair of finite adelic vectors has the coordinatewise local pairing. -/
theorem finiteIntegralAdeleBaseChange_pairing_apply
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K))
    (x y : TensorProduct (𝓞 K)
      (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier)
    (v : HeightOneSpectrum (𝓞 K)) :
    ((baseChangeIntegral (𝓞 K)
      (FiniteIntegralAdeleRing (𝓞 K) K)).obj L.obj).obj.pairing x y v =
      ((baseChangeIntegral (𝓞 K) (v.adicCompletionIntegers K)).obj L.obj).obj.pairing
        (finiteAdeleLocalCarrierEquiv K L x v)
        (finiteAdeleLocalCarrierEquiv K L y v) := by
  rw [← baseChangeIntegralBilinMap_apply, ← baseChangeIntegralBilinMap_apply]
  exact congrFun (LinearMap.congr_fun
    (LinearMap.congr_fun (finiteIntegralAdelePairing_eq_localPairing K L) x) y) v

/-- The orthogonal group of the full ring-adelic scalar extension. -/
abbrev RingAdelicOrthogonalGroup
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  BilinModuleCat.OrthogonalGroup ((finiteRingAdeleBaseChange K).obj L).obj.obj

/-- The orthogonal group of the integral finite adelic scalar extension. -/
abbrev FiniteIntegralAdelicOrthogonalGroup
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  BilinModuleCat.OrthogonalGroup ((finiteIntegralAdeleBaseChange K).obj L).obj.obj

/-- Two finite projective integral lattices have the same genus when their adelic scalar
extensions are isometric. -/
def SameAdeleGenus
    (L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) : Prop :=
  Nonempty ((finiteRingAdeleBaseChange K).obj L ≅
    (finiteRingAdeleBaseChange K).obj M)

theorem sameAdeleGenus_refl
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    SameAdeleGenus K L L :=
  ⟨Iso.refl _⟩

theorem sameAdeleGenus_symm
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (h : SameAdeleGenus K L M) : SameAdeleGenus K M L := by
  obtain ⟨e⟩ := h
  exact ⟨e.symm⟩

theorem sameAdeleGenus_trans
    {L M N : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (hLM : SameAdeleGenus K L M) (hMN : SameAdeleGenus K M N) :
    SameAdeleGenus K L N := by
  obtain ⟨e⟩ := hLM
  obtain ⟨f⟩ := hMN
  exact ⟨e ≪≫ f⟩

/-- Adelic genus is an equivalence relation on finite projective integral lattices. -/
def adeleGenusSetoid : Setoid (FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) where
  r := SameAdeleGenus K
  iseqv := ⟨sameAdeleGenus_refl K, sameAdeleGenus_symm K,
    sameAdeleGenus_trans K⟩

end LeanCategories.Lattices.Valued

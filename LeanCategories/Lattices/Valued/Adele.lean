/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.IntegralAdeleRing
public import LeanCategories.Lattices.Valued.BaseChange
public import LeanCategories.Lattices.Valued.Completion
public import LeanCategories.Lattices.Valued.OrthogonalGroup
public import LeanCategories.Modules.Pi
public import LeanCategories.Modules.ProdRing
public import Mathlib.RingTheory.Flat.Equalizer

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
open scoped Pointwise

namespace LeanCategories.Lattices.Valued

universe u

variable (K : Type u) [Field K] [NumberField K]

variable (R : Type u) [CommRing R] [IsDedekindDomain R] [Algebra R K]
  [IsFractionRing R K]

/-- Scalar extension of integral lattices from `R` to its full ring adele ring. -/
def ringAdeleBaseChangeOf :
    IntegralLatticeCat R ⥤ IntegralLatticeCat (RingAdeleRingOf R K) :=
  baseChangeIntegral R (RingAdeleRingOf R K)

/-- Scalar extension of finite projective `R`-lattices to the full ring adele ring. -/
def finiteRingAdeleBaseChangeOf :
    FiniteProjectiveLatticeCat R R ⥤
      FiniteProjectiveLatticeCat (RingAdeleRingOf R K) (RingAdeleRingOf R K) :=
  baseChangeFiniteIntegral R (RingAdeleRingOf R K)

variable {R}

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

/-- The infinite and integral finite carriers of ring-adelic scalar extension. -/
abbrev RingAdeleComponentCarriers
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  TensorProduct (𝓞 K) (NumberField.InfiniteAdeleRing K) L.obj.obj.carrier ×
    TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier

local instance infiniteAdeleCarrierRingAdeleModule
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Module (RingAdeleRing K)
      (TensorProduct (𝓞 K) (NumberField.InfiniteAdeleRing K) L.obj.obj.carrier) :=
  Module.compHom _ (RingHom.fst _ _)

local instance integralFiniteAdeleCarrierRingAdeleModule
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Module (RingAdeleRing K)
      (TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier) :=
  Module.compHom _ (RingHom.snd _ _)

/-- Ring-adelic scalar extension splits into its two carriers as an integral linear equivalence. -/
def ringAdeleCarrierLinearEquiv
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    TensorProduct (𝓞 K) (RingAdeleRing K) L.obj.obj.carrier
      ≃ₗ[𝓞 K] RingAdeleComponentCarriers K L :=
  TensorProduct.prodLeft (𝓞 K) (𝓞 K)
    (NumberField.InfiniteAdeleRing K)
    (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier

/-- Ring-adelic scalar extension splits into its infinite and integral finite carriers. -/
def ringAdeleCarrierEquiv
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    TensorProduct (𝓞 K) (RingAdeleRing K) L.obj.obj.carrier
      ≃ₗ[RingAdeleRing K] RingAdeleComponentCarriers K L :=
  LinearEquiv.ofBijective
    { toFun := ringAdeleCarrierLinearEquiv K L
      map_add' := map_add (ringAdeleCarrierLinearEquiv K L)
      map_smul' := by
        intro a x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b x =>
            change ((a.1 * b.1) ⊗ₜ[𝓞 K] x, (a.2 * b.2) ⊗ₜ[𝓞 K] x) =
              (a.1 • (b.1 ⊗ₜ[𝓞 K] x), a.2 • (b.2 ⊗ₜ[𝓞 K] x))
            ext <;> simp [TensorProduct.smul_tmul']
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
    (ringAdeleCarrierLinearEquiv K L).bijective

@[simp]
theorem ringAdeleCarrierEquiv_tmul
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K))
    (a : RingAdeleRing K) (x : L.obj.obj.carrier) :
    ringAdeleCarrierEquiv K L (a ⊗ₜ[𝓞 K] x) =
      (a.1 ⊗ₜ[𝓞 K] x, a.2 ⊗ₜ[𝓞 K] x) :=
  rfl

/-- Scalar extension of finite projective lattices to the finite field adele ring. -/
def finiteFieldAdeleBaseChange :
    FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K) ⥤
      FiniteProjectiveLatticeCat
        (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 K) K) :=
  baseChangeFiniteIntegral (𝓞 K) (FiniteAdeleRing (𝓞 K) K)

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

/-- A family of isometries between the scalar extensions at every finite place. -/
abbrev FiniteAdeleLocalIsometryFamily
    (L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  (v : HeightOneSpectrum (𝓞 K)) →
    ((baseChangeIntegral (𝓞 K) (v.adicCompletionIntegers K)).obj L.obj).obj ≅
      ((baseChangeIntegral (𝓞 K) (v.adicCompletionIntegers K)).obj M.obj).obj

/-- A family of local isometries acts coordinatewise on the product of local carriers. -/
noncomputable def finiteAdeleLocalIsometryLinearEquiv
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : FiniteAdeleLocalIsometryFamily K L M) :
    FiniteAdeleLocalModuleProduct K L ≃ₗ[FiniteIntegralAdeleRing (𝓞 K) K]
      FiniteAdeleLocalModuleProduct K M where
  toFun x v := BilinModuleCat.linearEquivOfIso (e v) (x v)
  invFun x v := (BilinModuleCat.linearEquivOfIso (e v)).symm (x v)
  map_add' x y := by
    funext v
    exact map_add (BilinModuleCat.linearEquivOfIso (e v)) (x v) (y v)
  map_smul' a x := by
    funext v
    exact map_smul (BilinModuleCat.linearEquivOfIso (e v)) (a v) (x v)
  left_inv x := by
    funext v
    exact (BilinModuleCat.linearEquivOfIso (e v)).symm_apply_apply (x v)
  right_inv x := by
    funext v
    exact (BilinModuleCat.linearEquivOfIso (e v)).apply_symm_apply (x v)

/-- Placewise isometries assemble to an isometry of the integral finite adelic carriers. -/
noncomputable def finiteAdeleCarrierIsometryLinearEquiv
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : FiniteAdeleLocalIsometryFamily K L M) :
    TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier
      ≃ₗ[FiniteIntegralAdeleRing (𝓞 K) K]
    TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) M.obj.obj.carrier :=
  (finiteAdeleLocalCarrierAlgEquiv K L).trans <|
    (finiteAdeleLocalIsometryLinearEquiv K e).trans
      (finiteAdeleLocalCarrierAlgEquiv K M).symm

@[simp]
theorem finiteAdeleLocalCarrierAlgEquiv_apply_carrierIsometry
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : FiniteAdeleLocalIsometryFamily K L M)
    (x : TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K)
      L.obj.obj.carrier) (v : HeightOneSpectrum (𝓞 K)) :
    finiteAdeleLocalCarrierAlgEquiv K M
        (finiteAdeleCarrierIsometryLinearEquiv K e x) v =
      BilinModuleCat.linearEquivOfIso (e v)
        (finiteAdeleLocalCarrierAlgEquiv K L x v) :=
  by
    simp [finiteAdeleCarrierIsometryLinearEquiv,
      finiteAdeleLocalIsometryLinearEquiv]

theorem finiteAdeleLocalCarrierEquiv_apply_carrierIsometry
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : FiniteAdeleLocalIsometryFamily K L M)
    (x : TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K)
      L.obj.obj.carrier) (v : HeightOneSpectrum (𝓞 K)) :
    finiteAdeleLocalCarrierEquiv K M
        (finiteAdeleCarrierIsometryLinearEquiv K e x) v =
      BilinModuleCat.linearEquivOfIso (e v)
        (finiteAdeleLocalCarrierEquiv K L x v) := by
  exact finiteAdeleLocalCarrierAlgEquiv_apply_carrierIsometry K e x v

/-- The assembled carrier equivalence preserves the integral finite adelic form. -/
theorem finiteAdeleCarrierIsometryLinearEquiv_pairing
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : FiniteAdeleLocalIsometryFamily K L M)
    (x y : TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K)
      L.obj.obj.carrier) :
    ((baseChangeIntegral (𝓞 K)
      (FiniteIntegralAdeleRing (𝓞 K) K)).obj M.obj).obj.pairing
        (finiteAdeleCarrierIsometryLinearEquiv K e x)
        (finiteAdeleCarrierIsometryLinearEquiv K e y) =
      ((baseChangeIntegral (𝓞 K)
        (FiniteIntegralAdeleRing (𝓞 K) K)).obj L.obj).obj.pairing x y := by
  apply funext
  intro v
  rw [finiteIntegralAdeleBaseChange_pairing_apply K M,
    finiteIntegralAdeleBaseChange_pairing_apply K L]
  rw [finiteAdeleLocalCarrierEquiv_apply_carrierIsometry K e x v,
    finiteAdeleLocalCarrierEquiv_apply_carrierIsometry K e y v]
  exact BilinModuleCat.linearEquivOfIso_pairing (e v) _ _

/-- Placewise finite isometries assemble to an isometry after integral finite adelic base change. -/
noncomputable def finiteIntegralAdeleIsoOfLocalIsometries
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : FiniteAdeleLocalIsometryFamily K L M) :
    (finiteIntegralAdeleBaseChange K).obj L ≅
      (finiteIntegralAdeleBaseChange K).obj M := by
  let eBilin :
      ((baseChangeIntegral (𝓞 K)
        (FiniteIntegralAdeleRing (𝓞 K) K)).obj L.obj).obj ≅
      ((baseChangeIntegral (𝓞 K)
        (FiniteIntegralAdeleRing (𝓞 K) K)).obj M.obj).obj :=
    BilinModuleCat.isoMk (finiteAdeleCarrierIsometryLinearEquiv K e)
      (finiteAdeleCarrierIsometryLinearEquiv_pairing K e)
  let eLattice := ObjectProperty.isoMk (P := isLattice
    (FiniteIntegralAdeleRing (𝓞 K) K) (FiniteIntegralAdeleRing (𝓞 K) K)) eBilin
  exact ObjectProperty.isoMk
    (P := isFiniteProjectiveLattice
      (FiniteIntegralAdeleRing (𝓞 K) K) (FiniteIntegralAdeleRing (𝓞 K) K)) eLattice

/-- Forget an integral finite adelic lattice isomorphism to its formed-module isomorphism. -/
def finiteIntegralAdeleBilinIso
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : (finiteIntegralAdeleBaseChange K).obj L ≅
      (finiteIntegralAdeleBaseChange K).obj M) :
    ((baseChangeIntegral (𝓞 K)
      (FiniteIntegralAdeleRing (𝓞 K) K)).obj L.obj).obj ≅
      ((baseChangeIntegral (𝓞 K)
        (FiniteIntegralAdeleRing (𝓞 K) K)).obj M.obj).obj :=
  (ObjectProperty.ι (isLattice
    (FiniteIntegralAdeleRing (𝓞 K) K)
    (FiniteIntegralAdeleRing (𝓞 K) K))).mapIso <|
    (ObjectProperty.ι (isFiniteProjectiveLattice
      (FiniteIntegralAdeleRing (𝓞 K) K)
      (FiniteIntegralAdeleRing (𝓞 K) K))).mapIso e

/-- An integral finite adelic isomorphism in the product-of-local-carriers presentation. -/
noncomputable def finiteAdeleLocalProductLinearEquivOfIso
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : (finiteIntegralAdeleBaseChange K).obj L ≅
      (finiteIntegralAdeleBaseChange K).obj M) :
    FiniteAdeleLocalModuleProduct K L ≃ₗ[FiniteIntegralAdeleRing (𝓞 K) K]
      FiniteAdeleLocalModuleProduct K M :=
  (finiteAdeleLocalCarrierAlgEquiv K L).symm |>.trans <|
    (BilinModuleCat.linearEquivOfIso (finiteIntegralAdeleBilinIso K e)).trans
      (finiteAdeleLocalCarrierAlgEquiv K M)

local instance finiteAdelePlaceDecidableEq :
    DecidableEq (HeightOneSpectrum (𝓞 K)) :=
  Classical.decEq _

/-- Restrict an integral finite adelic isomorphism to one finite place. -/
noncomputable def finiteAdeleLocalLinearEquivOfIso
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : (finiteIntegralAdeleBaseChange K).obj L ≅
      (finiteIntegralAdeleBaseChange K).obj M)
    (v : HeightOneSpectrum (𝓞 K)) :
    TensorProduct (𝓞 K) (v.adicCompletionIntegers K) L.obj.obj.carrier
      ≃ₗ[v.adicCompletionIntegers K]
    TensorProduct (𝓞 K) (v.adicCompletionIntegers K) M.obj.obj.carrier :=
  LinearEquiv.piRingCoordinate
    (fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletionIntegers K)
    (fun v ↦ TensorProduct (𝓞 K) (v.adicCompletionIntegers K) L.obj.obj.carrier)
    (fun v ↦ TensorProduct (𝓞 K) (v.adicCompletionIntegers K) M.obj.obj.carrier)
    (finiteAdeleLocalProductLinearEquivOfIso K e) v

@[simp]
theorem finiteAdeleLocalCarrierEquiv_symm_single_apply
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K))
    (v : HeightOneSpectrum (𝓞 K))
    (x : TensorProduct (𝓞 K) (v.adicCompletionIntegers K) L.obj.obj.carrier) :
    finiteAdeleLocalCarrierEquiv K L
        ((finiteAdeleLocalCarrierAlgEquiv K L).symm (Pi.single v x)) v = x := by
  change finiteAdeleLocalCarrierAlgEquiv K L
      ((finiteAdeleLocalCarrierAlgEquiv K L).symm (Pi.single v x)) v = x
  rw [LinearEquiv.apply_symm_apply, Pi.single_eq_same]

@[simp]
theorem finiteAdeleLocalCarrierEquiv_map_globalIso_single_apply
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : (finiteIntegralAdeleBaseChange K).obj L ≅
      (finiteIntegralAdeleBaseChange K).obj M)
    (v : HeightOneSpectrum (𝓞 K))
    (x : TensorProduct (𝓞 K) (v.adicCompletionIntegers K) L.obj.obj.carrier) :
    finiteAdeleLocalCarrierEquiv K M
        (BilinModuleCat.underlyingMap (finiteIntegralAdeleBilinIso K e).hom
          ((finiteAdeleLocalCarrierAlgEquiv K L).symm (Pi.single v x))) v =
      finiteAdeleLocalLinearEquivOfIso K e v x :=
  rfl

/-- The restriction of an integral finite adelic isomorphism preserves the local form. -/
theorem finiteAdeleLocalLinearEquivOfIso_pairing
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : (finiteIntegralAdeleBaseChange K).obj L ≅
      (finiteIntegralAdeleBaseChange K).obj M)
    (v : HeightOneSpectrum (𝓞 K))
    (x y : TensorProduct (𝓞 K) (v.adicCompletionIntegers K) L.obj.obj.carrier) :
    ((completeIntegralAtHeightOne (𝓞 K) K v).obj M.obj).obj.pairing
        (finiteAdeleLocalLinearEquivOfIso K e v x)
        (finiteAdeleLocalLinearEquivOfIso K e v y) =
      ((completeIntegralAtHeightOne (𝓞 K) K v).obj L.obj).obj.pairing x y := by
  let xA := (finiteAdeleLocalCarrierAlgEquiv K L).symm (Pi.single v x)
  let yA := (finiteAdeleLocalCarrierAlgEquiv K L).symm (Pi.single v y)
  have h := BilinModuleCat.linearEquivOfIso_pairing
    (finiteIntegralAdeleBilinIso K e) xA yA
  have hv := congrArg (fun z : FiniteIntegralAdeleRing (𝓞 K) K ↦ z v) h
  rw [finiteIntegralAdeleBaseChange_pairing_apply K M,
    finiteIntegralAdeleBaseChange_pairing_apply K L] at hv
  change
    ((baseChangeIntegral (𝓞 K) (v.adicCompletionIntegers K)).obj M.obj).obj.pairing
        (finiteAdeleLocalLinearEquivOfIso K e v x)
        (finiteAdeleLocalLinearEquivOfIso K e v y) =
      ((baseChangeIntegral (𝓞 K) (v.adicCompletionIntegers K)).obj L.obj).obj.pairing x y
  simpa [xA, yA] using hv

/-- Restrict an integral finite adelic isomorphism to a local formed-module isomorphism. -/
noncomputable def finiteAdeleLocalIsoOfIso
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : (finiteIntegralAdeleBaseChange K).obj L ≅
      (finiteIntegralAdeleBaseChange K).obj M)
    (v : HeightOneSpectrum (𝓞 K)) :
    ((completeIntegralAtHeightOne (𝓞 K) K v).obj L.obj).obj ≅
      ((completeIntegralAtHeightOne (𝓞 K) K v).obj M.obj).obj :=
  BilinModuleCat.isoMk (finiteAdeleLocalLinearEquivOfIso K e v)
    (finiteAdeleLocalLinearEquivOfIso_pairing K e v)

/-- Isometry after scalar extension to the integral finite adele ring. -/
def IsFiniteIntegrallyAdelicallyIsometric
    (L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) : Prop :=
  Nonempty ((finiteIntegralAdeleBaseChange K).obj L ≅
    (finiteIntegralAdeleBaseChange K).obj M)

/-- Isometry after scalar extension at every finite place. -/
def IsIsometricAtEveryFinitePlace
    (L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K),
    Nonempty (((completeIntegralAtHeightOne (𝓞 K) K v).obj L.obj).obj ≅
      ((completeIntegralAtHeightOne (𝓞 K) K v).obj M.obj).obj)

/-- Integral finite adelic isometry is equivalent to isometry at every finite place. -/
theorem isFiniteIntegrallyAdelicallyIsometric_iff_isIsometricAtEveryFinitePlace
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)} :
    IsFiniteIntegrallyAdelicallyIsometric K L M ↔
      IsIsometricAtEveryFinitePlace K L M := by
  constructor
  · rintro ⟨e⟩ v
    exact ⟨finiteAdeleLocalIsoOfIso K e v⟩
  · intro h
    classical
    exact ⟨finiteIntegralAdeleIsoOfLocalIsometries K
      (fun v ↦ Classical.choice (h v))⟩

/-- The full ring-adelic pairing is the pair of its infinite and integral finite pairings. -/
theorem ringAdeleBaseChange_pairing_components
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K))
    (x y : TensorProduct (𝓞 K) (RingAdeleRing K) L.obj.obj.carrier) :
    baseChangeIntegralBilinMap (𝓞 K) (RingAdeleRing K) L.obj x y =
      (baseChangeIntegralBilinMap (𝓞 K)
          (NumberField.InfiniteAdeleRing K) L.obj
          (ringAdeleCarrierEquiv K L x).1 (ringAdeleCarrierEquiv K L y).1,
        baseChangeIntegralBilinMap (𝓞 K)
          (FiniteIntegralAdeleRing (𝓞 K) K) L.obj
          (ringAdeleCarrierEquiv K L x).2 (ringAdeleCarrierEquiv K L y).2) := by
  induction x using TensorProduct.induction_on with
  | zero => apply Prod.ext <;> simp
  | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => apply Prod.ext <;> simp
      | tmul b y =>
          simp only [baseChangeIntegralBilinMap_tmul, ringAdeleCarrierEquiv_tmul]
          rfl
      | add y₁ y₂ hy₁ hy₂ =>
          apply Prod.ext <;>
            simp_all only [map_add, Prod.fst_add, Prod.snd_add]
  | add x₁ x₂ hx₁ hx₂ =>
      apply Prod.ext <;>
        simp_all only [map_add, LinearMap.add_apply, Prod.fst_add, Prod.snd_add]

/-- A pair of infinite and integral finite formed-module isometries. -/
abbrev RingAdeleComponentIsometryPair
    (L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  (((baseChangeIntegral (𝓞 K) (NumberField.InfiniteAdeleRing K)).obj L.obj).obj ≅
      ((baseChangeIntegral (𝓞 K) (NumberField.InfiniteAdeleRing K)).obj M.obj).obj) ×
    (((baseChangeIntegral (𝓞 K)
      (FiniteIntegralAdeleRing (𝓞 K) K)).obj L.obj).obj ≅
      ((baseChangeIntegral (𝓞 K)
        (FiniteIntegralAdeleRing (𝓞 K) K)).obj M.obj).obj)

/-- Component isometries assemble to a full ring-adelic carrier equivalence. -/
noncomputable def ringAdeleCarrierIsometryLinearEquiv
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : RingAdeleComponentIsometryPair K L M) :
    TensorProduct (𝓞 K) (RingAdeleRing K) L.obj.obj.carrier
      ≃ₗ[RingAdeleRing K]
    TensorProduct (𝓞 K) (RingAdeleRing K) M.obj.obj.carrier :=
  (ringAdeleCarrierEquiv K L).trans <|
    (LinearEquiv.prodRing _ _ _ _ _ _
      (BilinModuleCat.linearEquivOfIso e.1)
      (BilinModuleCat.linearEquivOfIso e.2)).trans
        (ringAdeleCarrierEquiv K M).symm

/-- The assembled full ring-adelic carrier equivalence preserves the form. -/
theorem ringAdeleCarrierIsometryLinearEquiv_pairing
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : RingAdeleComponentIsometryPair K L M)
    (x y : TensorProduct (𝓞 K) (RingAdeleRing K) L.obj.obj.carrier) :
    baseChangeIntegralBilinMap (𝓞 K) (RingAdeleRing K) M.obj
        (ringAdeleCarrierIsometryLinearEquiv K e x)
        (ringAdeleCarrierIsometryLinearEquiv K e y) =
      baseChangeIntegralBilinMap (𝓞 K) (RingAdeleRing K) L.obj x y := by
  have hinf (z) :
        (ringAdeleCarrierEquiv K M
          (ringAdeleCarrierIsometryLinearEquiv K e z)).1 =
        BilinModuleCat.linearEquivOfIso e.1 (ringAdeleCarrierEquiv K L z).1 :=
    by
      change
        (ringAdeleCarrierEquiv K M
          ((ringAdeleCarrierEquiv K M).symm
            (BilinModuleCat.linearEquivOfIso e.1 (ringAdeleCarrierEquiv K L z).1,
              BilinModuleCat.linearEquivOfIso e.2
                (ringAdeleCarrierEquiv K L z).2))).1 = _
      rw [(ringAdeleCarrierEquiv K M).apply_symm_apply]
  have hfin (z) :
        (ringAdeleCarrierEquiv K M
          (ringAdeleCarrierIsometryLinearEquiv K e z)).2 =
        BilinModuleCat.linearEquivOfIso e.2 (ringAdeleCarrierEquiv K L z).2 :=
    by
      change
        (ringAdeleCarrierEquiv K M
          ((ringAdeleCarrierEquiv K M).symm
            (BilinModuleCat.linearEquivOfIso e.1 (ringAdeleCarrierEquiv K L z).1,
              BilinModuleCat.linearEquivOfIso e.2
                (ringAdeleCarrierEquiv K L z).2))).2 = _
      rw [(ringAdeleCarrierEquiv K M).apply_symm_apply]
  apply Prod.ext
  · rw [show
        (baseChangeIntegralBilinMap (𝓞 K) (RingAdeleRing K) M.obj
          (ringAdeleCarrierIsometryLinearEquiv K e x)
          (ringAdeleCarrierIsometryLinearEquiv K e y)).1 = _ from
        congrArg Prod.fst (ringAdeleBaseChange_pairing_components K M _ _)]
    rw [show
        (baseChangeIntegralBilinMap (𝓞 K) (RingAdeleRing K) L.obj x y).1 = _ from
        congrArg Prod.fst (ringAdeleBaseChange_pairing_components K L x y)]
    rw [hinf x, hinf y]
    exact BilinModuleCat.linearEquivOfIso_pairing e.1 _ _
  · rw [show
        (baseChangeIntegralBilinMap (𝓞 K) (RingAdeleRing K) M.obj
          (ringAdeleCarrierIsometryLinearEquiv K e x)
          (ringAdeleCarrierIsometryLinearEquiv K e y)).2 = _ from
        congrArg Prod.snd (ringAdeleBaseChange_pairing_components K M _ _)]
    rw [show
        (baseChangeIntegralBilinMap (𝓞 K) (RingAdeleRing K) L.obj x y).2 = _ from
        congrArg Prod.snd (ringAdeleBaseChange_pairing_components K L x y)]
    rw [hfin x, hfin y]
    exact BilinModuleCat.linearEquivOfIso_pairing e.2 _ _

/-- Component isometries assemble to a full ring-adelic formed-module isomorphism. -/
noncomputable def ringAdeleBilinIsoOfComponentIsometries
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : RingAdeleComponentIsometryPair K L M) :
    ((baseChangeIntegral (𝓞 K) (RingAdeleRing K)).obj L.obj).obj ≅
      ((baseChangeIntegral (𝓞 K) (RingAdeleRing K)).obj M.obj).obj :=
  BilinModuleCat.isoMk (ringAdeleCarrierIsometryLinearEquiv K e)
    (ringAdeleCarrierIsometryLinearEquiv_pairing K e)

/-- Forget a full ring-adelic lattice isomorphism to its formed-module isomorphism. -/
def ringAdeleBilinIso
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : (finiteRingAdeleBaseChange K).obj L ≅
      (finiteRingAdeleBaseChange K).obj M) :
    ((baseChangeIntegral (𝓞 K) (RingAdeleRing K)).obj L.obj).obj ≅
      ((baseChangeIntegral (𝓞 K) (RingAdeleRing K)).obj M.obj).obj :=
  (ObjectProperty.ι (isLattice (RingAdeleRing K) (RingAdeleRing K))).mapIso <|
    (ObjectProperty.ι (isFiniteProjectiveLattice
      (RingAdeleRing K) (RingAdeleRing K))).mapIso e

/-- A full ring-adelic isomorphism in the two-component carrier presentation. -/
noncomputable def ringAdeleComponentCarrierLinearEquivOfIso
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : (finiteRingAdeleBaseChange K).obj L ≅
      (finiteRingAdeleBaseChange K).obj M) :
    RingAdeleComponentCarriers K L ≃ₗ[RingAdeleRing K]
      RingAdeleComponentCarriers K M :=
  (ringAdeleCarrierEquiv K L).symm |>.trans <|
    (BilinModuleCat.linearEquivOfIso (ringAdeleBilinIso K e)).trans
      (ringAdeleCarrierEquiv K M)

/-- Restrict a full ring-adelic isomorphism to the infinite carrier. -/
noncomputable def ringAdeleInfiniteLinearEquivOfIso
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : (finiteRingAdeleBaseChange K).obj L ≅
      (finiteRingAdeleBaseChange K).obj M) :
    TensorProduct (𝓞 K) (NumberField.InfiniteAdeleRing K) L.obj.obj.carrier
      ≃ₗ[NumberField.InfiniteAdeleRing K]
    TensorProduct (𝓞 K) (NumberField.InfiniteAdeleRing K) M.obj.obj.carrier :=
  LinearEquiv.prodRingLeft _ _ _ _ _ _
    (ringAdeleComponentCarrierLinearEquivOfIso K e)

/-- Restrict a full ring-adelic isomorphism to the integral finite carrier. -/
noncomputable def ringAdeleIntegralFiniteLinearEquivOfIso
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : (finiteRingAdeleBaseChange K).obj L ≅
      (finiteRingAdeleBaseChange K).obj M) :
    TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier
      ≃ₗ[FiniteIntegralAdeleRing (𝓞 K) K]
    TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) M.obj.obj.carrier :=
  LinearEquiv.prodRingRight _ _ _ _ _ _
    (ringAdeleComponentCarrierLinearEquivOfIso K e)

/-- The infinite restriction preserves the scalar-extended form. -/
theorem ringAdeleInfiniteLinearEquivOfIso_pairing
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : (finiteRingAdeleBaseChange K).obj L ≅
      (finiteRingAdeleBaseChange K).obj M)
    (x y : TensorProduct (𝓞 K) (NumberField.InfiniteAdeleRing K) L.obj.obj.carrier) :
    baseChangeIntegralBilinMap (𝓞 K) (NumberField.InfiniteAdeleRing K) M.obj
        (ringAdeleInfiniteLinearEquivOfIso K e x)
        (ringAdeleInfiniteLinearEquivOfIso K e y) =
      baseChangeIntegralBilinMap (𝓞 K) (NumberField.InfiniteAdeleRing K) L.obj x y := by
  let xA := (ringAdeleCarrierEquiv K L).symm (x, 0)
  let yA := (ringAdeleCarrierEquiv K L).symm (y, 0)
  have h := BilinModuleCat.linearEquivOfIso_pairing (ringAdeleBilinIso K e) xA yA
  rw [← baseChangeIntegralBilinMap_apply, ← baseChangeIntegralBilinMap_apply] at h
  rw [ringAdeleBaseChange_pairing_components K M,
    ringAdeleBaseChange_pairing_components K L] at h
  change
    baseChangeIntegralBilinMap (𝓞 K) (NumberField.InfiniteAdeleRing K) M.obj
        ((ringAdeleCarrierEquiv K M
          (BilinModuleCat.underlyingMap (ringAdeleBilinIso K e).hom xA)).1)
        ((ringAdeleCarrierEquiv K M
          (BilinModuleCat.underlyingMap (ringAdeleBilinIso K e).hom yA)).1) = _
  simpa [xA, yA, ringAdeleInfiniteLinearEquivOfIso,
    ringAdeleComponentCarrierLinearEquivOfIso, LinearEquiv.prodRingLeft,
    BilinModuleCat.linearEquivOfIso_apply] using
      congrArg Prod.fst h

/-- The integral finite restriction preserves the scalar-extended form. -/
theorem ringAdeleIntegralFiniteLinearEquivOfIso_pairing
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : (finiteRingAdeleBaseChange K).obj L ≅
      (finiteRingAdeleBaseChange K).obj M)
    (x y : TensorProduct (𝓞 K)
      (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier) :
    baseChangeIntegralBilinMap (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) M.obj
        (ringAdeleIntegralFiniteLinearEquivOfIso K e x)
        (ringAdeleIntegralFiniteLinearEquivOfIso K e y) =
      baseChangeIntegralBilinMap (𝓞 K)
        (FiniteIntegralAdeleRing (𝓞 K) K) L.obj x y := by
  let xA := (ringAdeleCarrierEquiv K L).symm (0, x)
  let yA := (ringAdeleCarrierEquiv K L).symm (0, y)
  have h := BilinModuleCat.linearEquivOfIso_pairing (ringAdeleBilinIso K e) xA yA
  rw [← baseChangeIntegralBilinMap_apply, ← baseChangeIntegralBilinMap_apply] at h
  rw [ringAdeleBaseChange_pairing_components K M,
    ringAdeleBaseChange_pairing_components K L] at h
  change
    baseChangeIntegralBilinMap (𝓞 K)
        (FiniteIntegralAdeleRing (𝓞 K) K) M.obj
        ((ringAdeleCarrierEquiv K M
          (BilinModuleCat.underlyingMap (ringAdeleBilinIso K e).hom xA)).2)
        ((ringAdeleCarrierEquiv K M
          (BilinModuleCat.underlyingMap (ringAdeleBilinIso K e).hom yA)).2) = _
  simpa [xA, yA, ringAdeleIntegralFiniteLinearEquivOfIso,
    ringAdeleComponentCarrierLinearEquivOfIso, LinearEquiv.prodRingRight,
    BilinModuleCat.linearEquivOfIso_apply] using
      congrArg Prod.snd h

/-- Restrict a full ring-adelic isomorphism to its two component isometries. -/
noncomputable def ringAdeleComponentIsometriesOfIso
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : (finiteRingAdeleBaseChange K).obj L ≅
      (finiteRingAdeleBaseChange K).obj M) :
    RingAdeleComponentIsometryPair K L M :=
  (BilinModuleCat.isoMk (ringAdeleInfiniteLinearEquivOfIso K e)
      (ringAdeleInfiniteLinearEquivOfIso_pairing K e),
    BilinModuleCat.isoMk (ringAdeleIntegralFiniteLinearEquivOfIso K e)
      (ringAdeleIntegralFiniteLinearEquivOfIso_pairing K e))

/-- Component isometries assemble to an isomorphism of finite projective adelic lattices. -/
noncomputable def ringAdeleIsoOfComponentIsometries
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : RingAdeleComponentIsometryPair K L M) :
    (finiteRingAdeleBaseChange K).obj L ≅
      (finiteRingAdeleBaseChange K).obj M := by
  let eLattice := ObjectProperty.isoMk
    (P := isLattice (RingAdeleRing K) (RingAdeleRing K))
    (ringAdeleBilinIsoOfComponentIsometries K e)
  exact ObjectProperty.isoMk
    (P := isFiniteProjectiveLattice (RingAdeleRing K) (RingAdeleRing K)) eLattice
/-- The orthogonal group of the full ring-adelic scalar extension. -/
abbrev RingAdelicOrthogonalGroup
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  BilinModuleCat.OrthogonalGroup ((finiteRingAdeleBaseChange K).obj L).obj.obj

/-- The orthogonal group of the integral finite adelic scalar extension. -/
abbrev FiniteIntegralAdelicOrthogonalGroup
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  BilinModuleCat.OrthogonalGroup ((finiteIntegralAdeleBaseChange K).obj L).obj.obj

/-- The orthogonal group of the finite field-adelic scalar extension. -/
abbrev FiniteAdelicOrthogonalGroup
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  BilinModuleCat.OrthogonalGroup ((finiteFieldAdeleBaseChange K).obj L).obj.obj

/-- The finite adelic orthogonal group acts through its underlying linear equivalences. -/
instance finiteAdelicOrthogonalGroupMulAction
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    MulAction (FiniteAdelicOrthogonalGroup K L)
      (TensorProduct (𝓞 K) (FiniteAdeleRing (𝓞 K) K) L.obj.obj.carrier) where
  smul g x := g.1 x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The integral finite adelic carrier mapped into the finite field-adelic carrier. -/
def finiteIntegralAdeleLatticeMap
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier →ₗ[𝓞 K]
      TensorProduct (𝓞 K) (FiniteAdeleRing (𝓞 K) K) L.obj.obj.carrier :=
  LinearMap.rTensor L.obj.obj.carrier
    (FiniteIntegralAdeleRing.inclusion (𝓞 K) K).toLinearMap

@[simp]
theorem finiteIntegralAdeleLatticeMap_tmul
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K))
    (a : FiniteIntegralAdeleRing (𝓞 K) K) (x : L.obj.obj.carrier) :
    finiteIntegralAdeleLatticeMap K L (a ⊗ₜ[𝓞 K] x) =
      FiniteIntegralAdeleRing.inclusion (𝓞 K) K a ⊗ₜ[𝓞 K] x := by
  rfl

/-- The integral finite adelic carrier embeds into the finite field-adelic carrier. -/
theorem finiteIntegralAdeleLatticeMap_injective
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Function.Injective (finiteIntegralAdeleLatticeMap K L) := by
  letI : Module.Projective (𝓞 K) L.obj.obj.carrier := L.obj.property.1
  let f := (FiniteIntegralAdeleRing.inclusion (𝓞 K) K).toLinearMap
  change Function.Injective (LinearMap.rTensor L.obj.obj.carrier f)
  apply Module.Flat.rTensor_preserves_injective_linearMap
  exact FiniteIntegralAdeleRing.inclusion_injective (𝓞 K) K

/-- The integral finite adelic lattice inside the finite field-adelic carrier. -/
def finiteIntegralAdeleLattice
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Set (TensorProduct (𝓞 K) (FiniteAdeleRing (𝓞 K) K) L.obj.obj.carrier) :=
  Set.range (finiteIntegralAdeleLatticeMap K L)

/-- The two maps whose equalizer is the intersection of `K` and the integral finite adeles. -/
def finiteAdeleIntersectionLeftMap :
    (K × FiniteIntegralAdeleRing (𝓞 K) K) →ₗ[𝓞 K]
      FiniteAdeleRing (𝓞 K) K :=
  (RingAdeleRing.fieldFiniteDiagonal K).toLinearMap.comp
    (LinearMap.fst (𝓞 K) K (FiniteIntegralAdeleRing (𝓞 K) K))

def finiteAdeleIntersectionRightMap :
    (K × FiniteIntegralAdeleRing (𝓞 K) K) →ₗ[𝓞 K]
      FiniteAdeleRing (𝓞 K) K :=
  (FiniteIntegralAdeleRing.inclusion (𝓞 K) K).toLinearMap.comp
    (LinearMap.snd (𝓞 K) K (FiniteIntegralAdeleRing (𝓞 K) K))

/-- The module pullback of the rational and integral finite adelic scalar extensions. -/
abbrev FiniteAdeleLatticeIntersectionPullback
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  LinearMap.eqLocus
    (TensorProduct.AlgebraTensorModule.lTensor (𝓞 K) L.obj.obj.carrier
      (finiteAdeleIntersectionLeftMap K))
    (TensorProduct.AlgebraTensorModule.lTensor (𝓞 K) L.obj.obj.carrier
      (finiteAdeleIntersectionRightMap K))

/-- The coefficient-ring intersection, viewed as a linear equalizer. -/
def integerIntersectionLinearEquiv :
    (𝓞 K) ≃ₗ[𝓞 K] LinearMap.eqLocus
      (finiteAdeleIntersectionLeftMap K) (finiteAdeleIntersectionRightMap K) :=
  (RingAdeleRing.integerIntersectionAlgEquiv K).toLinearEquiv

/-- A finite projective lattice is the pullback of its rational and integral finite adelic
extensions inside its finite field-adelic extension. -/
def finiteAdeleLatticeIntersectionEquiv
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    L.obj.obj.carrier ≃ₗ[𝓞 K] FiniteAdeleLatticeIntersectionPullback K L := by
  letI : Module.Projective (𝓞 K) L.obj.obj.carrier := L.obj.property.1
  exact (TensorProduct.lid (𝓞 K) L.obj.obj.carrier).symm |>.trans
    (TensorProduct.comm (𝓞 K) (𝓞 K) L.obj.obj.carrier) |>.trans
    (LinearEquiv.lTensor L.obj.obj.carrier (integerIntersectionLinearEquiv K)) |>.trans
    (LinearMap.tensorEqLocusEquiv (𝓞 K) L.obj.obj.carrier
      (finiteAdeleIntersectionLeftMap K) (finiteAdeleIntersectionRightMap K))

/-- The stabilizer of the integral finite adelic lattice in the finite adelic orthogonal group. -/
abbrev FiniteIntegralAdeleLatticeStabilizer
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  MulAction.stabilizer (FiniteAdelicOrthogonalGroup K L)
    (finiteIntegralAdeleLattice K L)

/-- Two finite projective integral lattices have the same genus when their adelic scalar
extensions are isometric. -/
def SameAdeleGenus
    (L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) : Prop :=
  Nonempty ((finiteRingAdeleBaseChange K).obj L ≅
    (finiteRingAdeleBaseChange K).obj M)

/-- Isometry after scalar extension to the infinite adele ring. -/
def IsInfinitelyAdelicallyIsometric
    (L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) : Prop :=
  Nonempty
    (((baseChangeIntegral (𝓞 K) (NumberField.InfiniteAdeleRing K)).obj L.obj).obj ≅
      ((baseChangeIntegral (𝓞 K) (NumberField.InfiniteAdeleRing K)).obj M.obj).obj)

/-- Full ring-adelic genus is equivalent to its infinite and integral finite parts. -/
theorem sameAdeleGenus_iff_infinite_and_finite
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)} :
    SameAdeleGenus K L M ↔
      IsInfinitelyAdelicallyIsometric K L M ∧
        IsFiniteIntegrallyAdelicallyIsometric K L M := by
  constructor
  · rintro ⟨e⟩
    let components := ringAdeleComponentIsometriesOfIso K e
    exact ⟨⟨components.1⟩, ⟨ObjectProperty.isoMk
      (P := isFiniteProjectiveLattice
        (FiniteIntegralAdeleRing (𝓞 K) K)
        (FiniteIntegralAdeleRing (𝓞 K) K))
      (ObjectProperty.isoMk
        (P := isLattice (FiniteIntegralAdeleRing (𝓞 K) K)
          (FiniteIntegralAdeleRing (𝓞 K) K)) components.2)⟩⟩
  · rintro ⟨⟨eInfinite⟩, ⟨eFinite⟩⟩
    exact ⟨ringAdeleIsoOfComponentIsometries K
      (eInfinite, finiteIntegralAdeleBilinIso K eFinite)⟩

/-- Full ring-adelic genus is equivalent to infinite isometry and isometry at every finite place. -/
theorem sameAdeleGenus_iff_isometric_at_every_place
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)} :
    SameAdeleGenus K L M ↔
      IsInfinitelyAdelicallyIsometric K L M ∧
        IsIsometricAtEveryFinitePlace K L M := by
  rw [sameAdeleGenus_iff_infinite_and_finite,
    isFiniteIntegrallyAdelicallyIsometric_iff_isIsometricAtEveryFinitePlace]

/-- The finite place of `ℚ` corresponding to a rational prime. -/
noncomputable def rationalFinitePlace (p : Nat.Primes) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p

/-- Isometry at every finite place of `ℚ`, indexed by the corresponding rational prime. -/
noncomputable def IsIsometricAtEveryRationalPrime
    (L M : FiniteProjectiveLatticeCat (𝓞 ℚ) (𝓞 ℚ)) : Prop :=
  ∀ p : Nat.Primes,
    Nonempty
      (((completeIntegralAtHeightOne (𝓞 ℚ) ℚ
        (rationalFinitePlace p)).obj
          L.obj).obj ≅
        ((completeIntegralAtHeightOne (𝓞 ℚ) ℚ
          (rationalFinitePlace p)).obj
            M.obj).obj)

/-- For rational lattices, the finite-place condition can be indexed by rational primes. -/
theorem sameAdeleGenus_rat_iff_isometric_at_infinity_and_every_rational_prime
    (L M : FiniteProjectiveLatticeCat (𝓞 ℚ) (𝓞 ℚ)) :
    SameAdeleGenus ℚ L M ↔
      IsInfinitelyAdelicallyIsometric ℚ L M ∧
        IsIsometricAtEveryRationalPrime L M := by
  rw [sameAdeleGenus_iff_isometric_at_every_place]
  apply and_congr Iff.rfl
  constructor
  · intro h p
    exact h (rationalFinitePlace p)
  · intro h v
    have hv : rationalFinitePlace
        (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v) = v :=
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v
    rw [← hv]
    exact h (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v)

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

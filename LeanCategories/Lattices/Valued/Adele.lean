/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.IntegralAdeleRing
public import LeanCategories.Lattices.Valued.BaseChange
public import LeanCategories.Lattices.Valued.OrthogonalGroup
public import LeanCategories.Modules.Pi

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
    ((baseChangeIntegral (𝓞 K) (v.adicCompletionIntegers K)).obj M.obj).obj.pairing
        (finiteAdeleLocalLinearEquivOfIso K e v x)
        (finiteAdeleLocalLinearEquivOfIso K e v y) =
      ((baseChangeIntegral (𝓞 K) (v.adicCompletionIntegers K)).obj L.obj).obj.pairing x y := by
  let xA := (finiteAdeleLocalCarrierAlgEquiv K L).symm (Pi.single v x)
  let yA := (finiteAdeleLocalCarrierAlgEquiv K L).symm (Pi.single v y)
  have h := BilinModuleCat.linearEquivOfIso_pairing
    (finiteIntegralAdeleBilinIso K e) xA yA
  have hv := congrArg (fun z : FiniteIntegralAdeleRing (𝓞 K) K ↦ z v) h
  rw [finiteIntegralAdeleBaseChange_pairing_apply K M,
    finiteIntegralAdeleBaseChange_pairing_apply K L] at hv
  simpa [xA, yA] using hv

/-- Restrict an integral finite adelic isomorphism to a local formed-module isomorphism. -/
noncomputable def finiteAdeleLocalIsoOfIso
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (e : (finiteIntegralAdeleBaseChange K).obj L ≅
      (finiteIntegralAdeleBaseChange K).obj M)
    (v : HeightOneSpectrum (𝓞 K)) :
    ((baseChangeIntegral (𝓞 K) (v.adicCompletionIntegers K)).obj L.obj).obj ≅
      ((baseChangeIntegral (𝓞 K) (v.adicCompletionIntegers K)).obj M.obj).obj :=
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
    Nonempty (((baseChangeIntegral (𝓞 K) (v.adicCompletionIntegers K)).obj L.obj).obj ≅
      ((baseChangeIntegral (𝓞 K) (v.adicCompletionIntegers K)).obj M.obj).obj)

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
  one_smul x := rfl
  mul_smul g h x := rfl

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

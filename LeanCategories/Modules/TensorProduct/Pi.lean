/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Tensor products with arbitrary products

This file proves that tensoring with a finite projective module commutes with an arbitrary product.
-/

@[expose] public section

noncomputable section

namespace TensorProduct

universe u v w

variable (R : Type u) [CommRing R]
variable {ι : Type v} (A : ι → Type w)
variable [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]

/-- Exchange the two indices of a dependent product as a linear equivalence. -/
def piComm (n : ℕ) :
    ((i : ι) → Fin n → A i) ≃ₗ[R] (Fin n → (i : ι) → A i) where
  toFun x j i := x i j
  invFun x i j := x j i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical comparison for a finite free module and an arbitrary product. -/
def finFreePiRight (n : ℕ) :
    (Fin n → R) ⊗[R] ((i : ι) → A i) ≃ₗ[R]
      ((i : ι) → (Fin n → R) ⊗[R] A i) :=
  ((TensorProduct.comm R (Fin n → R) ((i : ι) → A i)).trans
      (piScalarRight R R ((i : ι) → A i) (Fin n))).trans
    (((LinearEquiv.piCongrRight fun i ↦
      (TensorProduct.comm R (Fin n → R) (A i)).trans
        (piScalarRight R R (A i) (Fin n))).trans (piComm R A n)).symm)

@[simp]
theorem finFreePiRight_tmul (n : ℕ) (x : Fin n → R) (a : (i : ι) → A i) :
    finFreePiRight R A n (x ⊗ₜ[R] a) = fun i ↦ x ⊗ₜ[R] a i := by
  ext i
  simp [finFreePiRight, piComm]
  apply (TensorProduct.comm R (Fin n → R) (A i)).injective
  simp
  apply (piScalarRight R R (A i) (Fin n)).injective
  ext j
  simp

/-- The canonical tensor-to-product map is bijective for a finite projective module. -/
theorem piRightHom_bijective_of_finite_projective
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] :
    Function.Bijective (piRightHom R R M A) := by
  obtain ⟨n, f, g, _hf, _hg, hfg⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R M
  let cF := piRightHom R R (Fin n → R) A
  let eF := finFreePiRight R A n
  have hcF : cF = eF := by
    ext x a i
    simp [cF, eF]
  have cF_bij : Function.Bijective cF := by
    rw [hcF]
    exact eF.bijective
  let mapTensor (h : M →ₗ[R] Fin n → R) (i : ι) :=
    TensorProduct.map h (LinearMap.id (R := R) (M := A i))
  let mapTensorBack (h : (Fin n → R) →ₗ[R] M) (i : ι) :=
    TensorProduct.map h (LinearMap.id (R := R) (M := A i))
  have natural_g (x : M ⊗[R] ((i : ι) → A i)) :
      cF (TensorProduct.map g (LinearMap.id (R := R) (M := (i : ι) → A i)) x) =
        fun i ↦ mapTensor g i ((piRightHom R R M A) x i) := by
    induction x using TensorProduct.induction_on with
    | zero => funext i; simp [cF, mapTensor]
    | tmul x a => rfl
    | add x y hx hy => funext i; simp only [map_add, hx, hy, Pi.add_apply]
  have natural_f (x : (Fin n → R) ⊗[R] ((i : ι) → A i)) :
      (piRightHom R R M A)
          (TensorProduct.map f (LinearMap.id (R := R) (M := (i : ι) → A i)) x) =
        fun i ↦ mapTensorBack f i (cF x i) := by
    induction x using TensorProduct.induction_on with
    | zero => funext i; simp [cF, mapTensorBack]
    | tmul x a => rfl
    | add x y hx hy => funext i; simp only [map_add, hx, hy, Pi.add_apply]
  constructor
  · intro x y hxy
    have hmap :
        TensorProduct.map g (LinearMap.id (R := R) (M := (i : ι) → A i)) x =
          TensorProduct.map g (LinearMap.id (R := R) (M := (i : ι) → A i)) y := by
      apply cF_bij.1
      rw [natural_g, natural_g, hxy]
    have := congrArg
      (TensorProduct.map f (LinearMap.id (R := R) (M := (i : ι) → A i))) hmap
    simpa [← TensorProduct.map_comp, ← LinearMap.comp_apply, hfg] using this
  · intro y
    let yg : (i : ι) → (Fin n → R) ⊗[R] A i :=
      fun i ↦ mapTensor g i (y i)
    obtain ⟨z, hz⟩ := cF_bij.2 yg
    refine ⟨TensorProduct.map f
      (LinearMap.id (R := R) (M := (i : ι) → A i)) z, ?_⟩
    rw [natural_f, hz]
    funext i
    change TensorProduct.map f (LinearMap.id (R := R) (M := A i))
      (TensorProduct.map g (LinearMap.id (R := R) (M := A i)) (y i)) = y i
    simpa [← TensorProduct.map_comp, ← LinearMap.comp_apply, hfg]

/-- Tensoring with a finite projective module commutes with an arbitrary product. -/
def piRightOfFiniteProjective
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] :
    M ⊗[R] ((i : ι) → A i) ≃ₗ[R] ((i : ι) → M ⊗[R] A i) :=
  LinearEquiv.ofBijective (piRightHom R R M A)
    (piRightHom_bijective_of_finite_projective R A M)

@[simp]
theorem piRightOfFiniteProjective_tmul
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (x : M) (a : (i : ι) → A i) :
    piRightOfFiniteProjective R A M (x ⊗ₜ[R] a) = fun i ↦ x ⊗ₜ[R] a i :=
  rfl

end TensorProduct

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Injective integer maps whose tensor maps are not injective

Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), printed p. 25,
FC04-C02-U047. The tensor of `2` and the nonzero element of `ZMod 2` is nonzero
in `2ℤ ⊗[ℤ] ZMod 2`, but its image in `ℤ ⊗[ℤ] ZMod 2` is zero.
The doubling map from printed p. 29 (FC04-C02-U060) is also treated directly:
it is injective over the integers, but its tensor with `ZMod 2` is the zero map.

The submodule is Mathlib's span of `2`. Its coordinate equivalence sends `2` to
`1`; tensoring that equivalence and applying the tensor unit isomorphism detects
the nonzero tensor. The inclusion-induced map, rather than an arbitrary zero map,
is then proved noninjective. The standard quotient model is connected to `ZMod 2`
by `Int.quotientSpanNatEquivZMod`.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

/-- Balancing moves the scalar `2` to the factor of characteristic two. -/
lemma int_two_tmul_zmod_two (x : ZMod 2) : (2 : ℤ) ⊗ₜ[ℤ] x = 0 := by
  have h : (2 : ℤ) • x = 0 := by
    rw [zsmul_eq_mul]
    change (2 : ZMod 2) * x = 0
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
  calc
    (2 : ℤ) ⊗ₜ[ℤ] x = (1 : ℤ) ⊗ₜ[ℤ] ((2 : ℤ) • x) := by
      simpa using (TensorProduct.smul_tmul (2 : ℤ) (1 : ℤ) x)
    _ = 0 := by rw [h, tmul_zero]

/-- The generator of the even-integer submodule has nonzero tensor with `1`. -/
lemma even_generator_tmul_one_ne_zero :
    (⟨2, Submodule.mem_span_singleton_self (2 : ℤ)⟩ : Submodule.span ℤ ({2} : Set ℤ))
        ⊗ₜ[ℤ] (1 : ZMod 2) ≠ 0 := by
  let e := LinearEquiv.coord ℤ ℤ (2 : ℤ) (by norm_num)
  intro h
  have hc := congrArg (fun t => TensorProduct.lid ℤ (ZMod 2)
    (TensorProduct.map e.toLinearMap (LinearMap.id : ZMod 2 →ₗ[ℤ] ZMod 2) t)) h
  have he : e ⟨2, Submodule.mem_span_singleton_self (2 : ℤ)⟩ = 1 :=
    LinearEquiv.coord_self ℤ ℤ (2 : ℤ) (by norm_num)
  simp [he] at hc

/-- Tensoring the actual inclusion `2ℤ ↪ ℤ` with `ZMod 2` is not injective. -/
lemma even_submodule_tensor_inclusion_not_injective :
    ¬ Function.Injective (TensorProduct.map
      (Submodule.span ℤ ({2} : Set ℤ)).subtype
      (LinearMap.id : ZMod 2 →ₗ[ℤ] ZMod 2)) := by
  intro h
  apply even_generator_tmul_one_ne_zero
  apply h
  simpa using int_two_tmul_zmod_two (1 : ZMod 2)

/-- Tensoring the integer doubling map with `ZMod 2` gives the zero linear map. -/
lemma int_two_tensor_map_eq_zero :
    TensorProduct.map (LinearMap.toSpanSingleton ℤ ℤ (2 : ℤ))
      (LinearMap.id : ZMod 2 →ₗ[ℤ] ZMod 2) = 0 := by
  apply TensorProduct.ext'
  intro a b
  change (a • (2 : ℤ)) ⊗ₜ[ℤ] b = 0
  rw [← TensorProduct.smul_tmul', int_two_tmul_zmod_two, smul_zero]

/-- The tensor of the doubling map is not injective; `1 ⊗ 1` detects the failure. -/
lemma int_two_tensor_map_not_injective :
    ¬ Function.Injective (TensorProduct.map (LinearMap.toSpanSingleton ℤ ℤ (2 : ℤ))
      (LinearMap.id : ZMod 2 →ₗ[ℤ] ZMod 2)) := by
  intro h
  have ht : (1 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 2) = 0 := by
    apply h
    simp only [int_two_tensor_map_eq_zero, LinearMap.zero_apply]
  have hz := congrArg (TensorProduct.lid ℤ (ZMod 2)) ht
  simp at hz

-- The original map is injective; tensoring, not the original sequence, causes the failure.
example : Function.Injective (LinearMap.toSpanSingleton ℤ ℤ (2 : ℤ)) := by
  intro a b h
  change a * 2 = b * 2 at h
  exact mul_right_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h

end TensorProduct

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
# A submodule inclusion whose tensor map is not injective

Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), printed p. 25,
FC04-C02-U047. The tensor of `2` and the nonzero element of `ZMod 2` is nonzero
in `2ℤ ⊗[ℤ] ZMod 2`, but its image in `ℤ ⊗[ℤ] ZMod 2` is zero.

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

end TensorProduct

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.IsotropicQuotientSignature

@[expose] public section

/-!
# One `ℤ`-action on a lattice carrier, so base change to `ℝ` uses Mathlib's tensor lemmas (#123)

The carrier of an integral lattice over `ℤ` is the coercion of a `ModuleCat ℤ` object, so its
`ℤ`-scalars would otherwise elaborate through the object's own field `ModuleCat.isModule` and
through the additive-group action `ZSMul.toSMul`, which are equal
(`AddCommGroup.subsingletonIntModule`) but not reducibly so. The canonical action
`AddCommGroup.toIntModule` — the one the mathlib3 `gsmul` refactor (#7255) made reducible for
every `AddCommGroup` — is pinned at the carrier's definition (`Fixed.lean`), which gives the
carrier one reducible `ℤ`-action across the base change.

These are the acceptance controls of #123: the `TensorProduct.CompatibleSMul ℤ ℤ ℝ` instance on
the carrier synthesizes with no local instance, and the base-change identity
`r ⊗ₜ[ℤ] (n • x) = (r * n) ⊗ₜ[ℤ] x` is closed by Mathlib's tensor lemmas
(`ModuleCat.zsmul_eq_smul`, `TensorProduct.smul_tmul`, `zsmul_eq_mul`, `mul_comm`), again with
no local instance. The real form is `ℝ ⊗[ℤ] L.obj.carrier`, Mathlib's base change, and every
statement of #122 keeps its shape.
-/

namespace LeanCategories.Lattices.Valued.CarrierIntActionTests

open LeanCategories.Modules.Bilinear.Valued
open scoped TensorProduct

variable {L : IntegralLatticeCat ℤ}

/-- The `TensorProduct.CompatibleSMul ℤ ℤ ℝ` instance on a lattice carrier, with no local
instance (#123): the carrier's `ℤ`-action is the canonical `AddCommGroup.toIntModule`, pinned
at the carrier's definition, so the class synthesizes. -/
example : TensorProduct.CompatibleSMul ℤ ℤ ℝ ↑L.obj.carrier := inferInstance

/-- The base-change identity of #123: a `ℤ`-scalar on the carrier side of a pure tensor is
absorbed into the `ℝ`-scalar, closed by Mathlib's tensor lemmas with no local instance. The
`ℤ`-scalar reaches the carrier through the additive-group action `ZSMul.toSMul`
(`Submodule.mem_span_singleton` route), so `ModuleCat.zsmul_eq_smul` first moves it onto the
carrier's `Module ℤ`-action, and then `TensorProduct.smul_tmul` carries it across the tensor. -/
example (r : ℝ) (n : ℤ) (x : L.obj.carrier) :
    r ⊗ₜ[ℤ] (n • x) = (r * n) ⊗ₜ[ℤ] x := by
  rw [ModuleCat.zsmul_eq_smul, ← TensorProduct.smul_tmul, zsmul_eq_mul, mul_comm]

end LeanCategories.Lattices.Valued.CarrierIntActionTests

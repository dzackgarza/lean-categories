/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Primitive elements of a coalgebra

Weibel, *An Introduction to Homological Algebra*, Primitive Elements 9.10.2, p. 363
(FC05-C09-U156).

The source writes the distinguished group-like element as `1`; accordingly this definition takes a
coalgebra whose underlying module carries a chosen `One`.  No compatibility beyond the displayed
primitive equation is required for the definition or for closure under the `k`-module operations.
The later graded-submodule statement is result-level.
-/

@[expose] public section

open scoped TensorProduct

namespace LeanCategories.Homological

universe u v

variable (k : Type u) [CommRing k]
variable (H : Type v) [AddCommGroup H] [Module k H] [Coalgebra k H] [One H]

/-- An element `x` is primitive when `Δ(x) = x ⊗ 1 + 1 ⊗ x`.

Source: Weibel, Primitive Elements 9.10.2, p. 363 (FC05-C09-U156). -/
def IsPrimitiveCoalgebraElement (x : H) : Prop :=
  Coalgebra.comul x = x ⊗ₜ[k] (1 : H) + (1 : H) ⊗ₜ[k] x

/-- The `k`-submodule `Prim(H)` of primitive elements.

Source: Weibel, Primitive Elements 9.10.2, p. 363 (FC05-C09-U156). -/
noncomputable def primitiveCoalgebraSubmodule : Submodule k H where
  carrier := {x | IsPrimitiveCoalgebraElement k H x}
  zero_mem' := by simp [IsPrimitiveCoalgebraElement]
  add_mem' := by
    intro x y hx hy
    change Coalgebra.comul (x + y) =
      (x + y) ⊗ₜ[k] (1 : H) + (1 : H) ⊗ₜ[k] (x + y)
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  smul_mem' := by
    intro r x hx
    change Coalgebra.comul (r • x) =
      (r • x) ⊗ₜ[k] (1 : H) + (1 : H) ⊗ₜ[k] (r • x)
    rw [map_smul, hx, smul_add]
    congr 1
    exact TensorProduct.smul_tmul r (1 : H) x

end LeanCategories.Homological

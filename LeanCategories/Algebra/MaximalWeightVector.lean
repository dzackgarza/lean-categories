/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.Base

/-!
# Maximal weight vectors

Definition-level realization of Humphreys FC14-C06-U004.  A maximal vector
of weight `λ` is a nonzero weight vector annihilated by every positive root
space for the chosen base.

The result that it is enough to test the simple-root spaces, dominance
consequences, and uniqueness statements are not included here.
-/

@[expose] public section

namespace LeanCategories.Algebra

open LieAlgebra LieModule Module

universe u v w

variable
  {K : Type u} {L : Type v} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  [LieModule.IsTriangularizable K H L]
  {M : Type w} [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]

/-- Humphreys' maximal-vector predicate for the positive system determined
by `b`. -/
def IsMaximalWeightVector
    (b : (LieAlgebra.IsKilling.rootSystem H).Base)
    (lam : Module.Dual K H) (v : M) : Prop :=
  v ≠ 0 ∧
    (∀ h : H, ⁅(h : L), v⁆ = lam h • v) ∧
    ∀ α : H.root, b.IsPos α →
      ∀ x ∈ rootSpace H (α : H → K), ⁅x, v⁆ = 0

end LeanCategories.Algebra

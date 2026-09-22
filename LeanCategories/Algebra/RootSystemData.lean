/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.SetTheory.Cardinal.NatCard

@[expose] public noncomputable section

namespace LeanCategories.Algebra

open scoped BigOperators

/-- Humphreys FC14-C03-U060: one half of the sum of the positive roots.
The strong-dominance and reflection identities are theorem content. -/
def halfSumPositiveRoots {E : Type*} [AddCommGroup E] [Module ℝ E]
    (positiveRoots : Finset E) : E :=
  (2 : ℝ)⁻¹ • positiveRoots.sum id

/-- Nonnegative positive-root multiplicity data with prescribed weighted sum. -/
def kostantPartitionSet {E : Type*} [AddCommMonoid E]
    (positiveRoots : Finset E) (nu : E) : Set (positiveRoots → ℕ) :=
  {m | ∑ alpha : positiveRoots, m alpha • (alpha : E) = nu}

/-- Humphreys FC14-C06-U060: partitions of `-lambda`; finiteness is theorem content. -/
def kostantPartitionNumber {E : Type*} [AddCommGroup E]
    (positiveRoots : Finset E) (lambda : E) : ℕ :=
  Nat.card (kostantPartitionSet positiveRoots (-lambda))

end LeanCategories.Algebra

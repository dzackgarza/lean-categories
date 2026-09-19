/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Basic

@[expose] public noncomputable section

namespace LeanCategories.Algebra

/-- Humphreys FC14-C03-U060: one half of the sum of the positive roots.
The strong-dominance and reflection identities are theorem content. -/
def halfSumPositiveRoots {E : Type*} [AddCommGroup E] [Module ℝ E]
    (positiveRoots : Finset E) : E :=
  (2 : ℝ)⁻¹ • positiveRoots.sum id

end LeanCategories.Algebra

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Weight multiplicity data

Humphreys FC14-C06-U025. A weight multiplicity is the dimension of the
corresponding ordinary weight space. This file records only that numerical
construction; support, Weyl invariance, and formal-character packaging are
result/downstream content.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v w

variable (K : Type u) (H : Type v) (V : Type w)
variable [Field K] [LieRing H] [LieAlgebra K H]
variable [AddCommGroup V] [Module K V] [LieRingModule H V] [LieModule K H V]

/-- Humphreys' multiplicity `m(lambda) = dim V_lambda`. -/
def weightMultiplicity (lambda : H → K) : ℕ :=
  Module.finrank K (LieModule.weightSpace V lambda)

end LeanCategories.Algebra

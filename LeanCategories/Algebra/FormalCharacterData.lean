/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.WeightData
public import LeanCategories.Algebra.WeightMultiplicityData

/-!
# Formal-character source data

Definition-level realization of Humphreys FC14-C06-U033.

For a finite-dimensional module, the pinned Mathlib weight type is finite.
Consequently the formal character can be written literally as the finite sum

  `sum_mu (dim V_mu) e(mu)`

without first proving a support-finiteness lemma.

The carrier here is the ambient integral group ring on weight functions.  In
Humphreys' semisimple characteristic-zero setting every occurring weight is
integral, so the same finite sum lies in the subgroup ring on the integral
weight lattice.  That integrality/support statement, as well as Weyl
invariance, is result content and is deliberately not built into this
definition.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v w

variable (K : Type u) (H : Type v) (V : Type w)
variable [Field K] [LieRing H] [LieAlgebra K H]
variable [LieRing.IsNilpotent H]
variable [AddCommGroup V] [Module K V] [LieRingModule H V] [LieModule K H V]
variable [FiniteDimensional K V]

/-- Humphreys' formal-character finite sum, represented in the ambient group
ring on weight functions before restricting its support to the integral weight
lattice. -/
def formalCharacterData : integralWeightGroupRing (H → K) := by
  classical
  exact
    ∑ mu : LieModule.Weight K H V,
      AddMonoidAlgebra.single (mu : H → K)
        (weightMultiplicity K H V mu : ℤ)

end LeanCategories.Algebra

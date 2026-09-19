/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Rank as the dimension of a Cartan subalgebra

This file records the definition in Humphreys, *Introduction to Lie Algebras and
Representation Theory*, Section 16.4, p. 86 (FC14-C04-U033). Over the standing
algebraically closed field of characteristic zero, the rank of a finite-dimensional Lie algebra
is the dimension of a Cartan subalgebra.

The Cartan subalgebra is selected by `Classical.epsilon` from Mathlib's intrinsic predicate
`LieSubalgebra.IsCartanSubalgebra`. Existence and the independence of its dimension from the
choice are separate results; they are not asserted here.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.LieAlgebra

variable (K L : Type*) [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

/-- A classically selected Cartan subalgebra of `L` in the source's setting. -/
def chosenCartanSubalgebra [CharZero K] [IsAlgClosed K] [FiniteDimensional K L] :
    LieSubalgebra K L :=
  Classical.epsilon fun H : LieSubalgebra K L => H.IsCartanSubalgebra

/-- Humphreys' rank of `L`: the dimension of a Cartan subalgebra. -/
def humphreysRank [CharZero K] [IsAlgClosed K] [FiniteDimensional K L] : ℕ :=
  Module.finrank K (chosenCartanSubalgebra K L)

end LeanCategories.LieAlgebra

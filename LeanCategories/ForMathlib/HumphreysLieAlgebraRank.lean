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

Cartan subalgebras are represented by Mathlib's intrinsic predicate
`LieSubalgebra.IsCartanSubalgebra`.  The rank is defined directly from the
set of their dimensions, so its declaration takes only the source Lie algebra
as input.  Existence of Cartan subalgebras and equality of all their dimensions
are separate results used only to identify this choice-free construction with
the usual phrase “the dimension of a Cartan subalgebra”.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.LieAlgebra

variable (K L : Type*) [Field K] [LieRing L] [LieAlgebra K L]

/-- Dimensions of Cartan subalgebras of `L`. -/
def cartanSubalgebraDimensions [CharZero K] [IsAlgClosed K] [FiniteDimensional K L] :
    Set ℕ :=
  {n | ∃ H : LieSubalgebra K L, H.IsCartanSubalgebra ∧ Module.finrank K H = n}

/-- Humphreys' rank of `L`, constructed from `L` alone as the least
dimension occurring among its Cartan subalgebras.

In the standing finite-dimensional characteristic-zero setting, Cartan
existence and conjugacy show that this is the dimension of every Cartan
subalgebra. Those facts are theorem-layer comparison results, not inputs to
the definition. -/
def humphreysRank [CharZero K] [IsAlgClosed K] [FiniteDimensional K L]
    : ℕ :=
  sInf (cartanSubalgebraDimensions K L)

end LeanCategories.LieAlgebra

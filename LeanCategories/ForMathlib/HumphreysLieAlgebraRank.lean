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

Cartan-subalgebra data are represented by Mathlib's intrinsic predicate
`LieSubalgebra.IsCartanSubalgebra`. Existence and independence of the
dimension from the choice are separate results; no arbitrary Lie subalgebra is
selected before those results.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.LieAlgebra

variable (K L : Type*) [Field K] [LieRing L] [LieAlgebra K L]

/-- Source-faithful Cartan-subalgebra data in Humphreys' setting. -/
abbrev CartanSubalgebraData [CharZero K] [IsAlgClosed K] [FiniteDimensional K L] :=
  {H : LieSubalgebra K L // H.IsCartanSubalgebra}

/-- Humphreys' rank of `L`: the dimension of a Cartan subalgebra. -/
def humphreysRank [CharZero K] [IsAlgClosed K] [FiniteDimensional K L]
    (H : CartanSubalgebraData K L) : ℕ :=
  Module.finrank K H.1

end LeanCategories.LieAlgebra

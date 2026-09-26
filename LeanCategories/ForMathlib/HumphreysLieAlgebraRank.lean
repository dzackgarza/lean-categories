/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.CartanExists
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Rank as the dimension of a Cartan subalgebra

Humphreys, *Introduction to Lie Algebras and Representation Theory*, §16.4,
defines the rank of a finite-dimensional Lie algebra as the dimension of a
Cartan subalgebra.  Mathlib constructs a Cartan subalgebra over an infinite
field as the Engel subalgebra of a regular element.  In the standing
algebraically closed characteristic-zero setting the field is infinite, so
this gives an actual source Cartan subalgebra from the Lie algebra itself.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.LieAlgebra

variable (K L : Type*) [Field K] [LieRing L] [LieAlgebra K L]

/-- A regular element whose Engel subalgebra is Cartan, supplied by Mathlib's
Cartan-existence theorem. -/
noncomputable def humphreysCartanElement
    [CharZero K] [IsAlgClosed K] [FiniteDimensional K L] : L :=
  Classical.choose (LieAlgebra.exists_isCartanSubalgebra_engel K L)

/-- The Cartan subalgebra constructed from the regular element above. -/
noncomputable def humphreysCartanSubalgebra
    [CharZero K] [IsAlgClosed K] [FiniteDimensional K L] : LieSubalgebra K L :=
  LieSubalgebra.engel K (humphreysCartanElement K L)

/-- Humphreys' rank of `L`: the dimension of the constructed Cartan subalgebra. -/
def humphreysRank [CharZero K] [IsAlgClosed K] [FiniteDimensional K L] : ℕ :=
  Module.finrank K (humphreysCartanSubalgebra K L)

end LeanCategories.LieAlgebra

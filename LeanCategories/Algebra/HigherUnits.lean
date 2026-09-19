/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Higher-unit filtration data

Definition-level realization of Neukirch FC09-C02-U041.

For an ideal `I` of a commutative ring, the `n`th higher-unit layer is the set
of units congruent to `1` modulo `I ^ n`.  In the valuation-ring application
`I` is the maximal ideal.  Sweep III records this underlying filtration only;
subgroup closure, monotonicity, neighbourhood-basis statements, and quotient
identifications are result content.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

variable {R : Type u} [CommRing R]

/-- The `n`th higher-unit layer attached to an ideal `I`:
`U^(n) = {u : Rˣ | u - 1 ∈ I^n}`. -/
def higherUnitSet (I : Ideal R) (n : ℕ) : Set Rˣ :=
  {u | (u : R) - 1 ∈ I ^ n}

/-- Principal units are the first higher-unit layer. -/
abbrev principalUnitSet (I : Ideal R) : Set Rˣ := higherUnitSet I 1

end LeanCategories.Algebra

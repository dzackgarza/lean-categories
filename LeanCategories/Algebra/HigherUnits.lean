/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Order.Floor.Ring

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

/-- Serre's higher-unit notation for a local ring:
`U_R^n = {u : Rˣ | u - 1 ∈ m_R^n}` (FC10-C12-U006). -/
abbrev localHigherUnitSet [IsLocalRing R] (n : ℕ) : Set Rˣ :=
  higherUnitSet (IsLocalRing.maximalIdeal R) n

/-- Serre's principal-unit layer `U_R^1` for a local ring
(FC10-C12-U006). -/
abbrev localPrincipalUnitSet [IsLocalRing R] : Set Rˣ :=
  localHigherUnitSet (R := R) 1

/-- Serre's real-index higher-unit notation: use the least natural level at
least `v`.  For the source's intended range `0 ≤ v`, this is exactly
`U^v = U^⌈v⌉`.  The definition is total on `ℝ`, avoiding a proof-valued
nonnegative-real index. -/
def realHigherUnitSet (I : Ideal R) (v : ℝ) : Set Rˣ :=
  higherUnitSet I ⌈v⌉₊

end LeanCategories.Algebra

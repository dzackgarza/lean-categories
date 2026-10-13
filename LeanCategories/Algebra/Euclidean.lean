/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.EuclideanDomain.Defs
public import Mathlib.RingTheory.Ideal.Basic

/-!
# Universal side divisors

Definitional material from Dummit--Foote, *Abstract Algebra*, 3rd ed., Chapter 8.

`IsUniversalSideDivisor` is adapted from `franv314/non-euclidean-pid`, commit
`087a99dc84ea7f0f70f614556f02111df63dd103`,
`NonEuclideanPid/NotEuclidean.lean` (MIT).

-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-- A nonzero nonunit `u` is a universal side divisor when every residue class
modulo `u` has a representative that is zero or a unit. This is FC01-C08-U023.

Adapted from `is_universal_side_divisor` in `franv314/non-euclidean-pid` at
commit `087a99dc84ea7f0f70f614556f02111df63dd103`. -/
def IsUniversalSideDivisor (u : R) : Prop :=
  u ≠ 0 ∧ ¬ IsUnit u ∧
    ∀ x : R, ∃ q r : R, x = q * u + r ∧ (r = 0 ∨ IsUnit r)

end LeanCategories.Algebra

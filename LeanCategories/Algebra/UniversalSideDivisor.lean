/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Ring.Divisibility.Basic

/-!
# Universal side divisors

Dummit--Foote call a nonzero nonunit `u` in an integral domain a universal side
divisor when every residue class modulo `u` has a representative that is zero
or a unit (`FC01-C08-U023`).

The predicates are ported from `franv314/non-euclidean-pid` commit
`087a99dc84ea7f0f70f614556f02111df63dd103`,
`NonEuclideanPid/NotEuclidean.lean` (MIT).  The external source calls the
representative set `small` and the main predicate `is_universal_side_divisor`.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

variable (R : Type u) [CommRing R] [IsDomain R]

/-- The source set `R~ = Rˣ ∪ {0}` of allowed residue representatives. -/
def universalSideRepresentatives : Set R :=
  {x | x = 0 ∨ IsUnit x}

/-- A nonzero nonunit `u` is a universal side divisor when every element is
congruent modulo `u` to zero or to a unit. -/
def IsUniversalSideDivisor (u : R) : Prop :=
  u ∉ universalSideRepresentatives R ∧
    ∀ x : R, ∃ q z : R, x = u * q + z ∧ z ∈ universalSideRepresentatives R

end LeanCategories.Algebra

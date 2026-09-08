/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.EuclideanDomain.Defs
public import Mathlib.RingTheory.Ideal.Basic

/-!
# Domain norms and Dedekind--Hasse conditions

Definitional material from Dummit--Foote, *Abstract Algebra*, 3rd ed., Chapter 8.
The source's weak notion of norm is kept as an ordinary function `R → ℕ`; the
mathematical conditions are predicates on that function rather than extra structure.

`IsUniversalSideDivisor` is adapted from `franv314/non-euclidean-pid`, commit
`087a99dc84ea7f0f70f614556f02111df63dd103`,
`NonEuclideanPid/NotEuclidean.lean` (MIT).

`IsDedekindHasseNorm` uses the source's positive integer-valued norm formulation.
The Sweep-II reference `DedekindHasseDomain` in the same repository and commit,
`NonEuclideanPid/PrincipalIdeal.lean` (MIT), packages the corresponding descent
condition by an arbitrary well-founded relation; it is a reference for the descent
interface, not a replacement for the source definition.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-- A Dummit--Foote domain norm is a nonnegative integer-valued function that
vanishes at zero. Since the codomain is `ℕ`, nonnegativity is automatic.
This is FC01-C08-U001. -/
def IsDomainNorm (N : R → ℕ) : Prop := N 0 = 0

/-- A domain norm is positive when it is strictly positive away from zero. -/
def IsPositiveDomainNorm (N : R → ℕ) : Prop :=
  IsDomainNorm N ∧ ∀ a : R, a ≠ 0 → 0 < N a

/-- A nonzero nonunit `u` is a universal side divisor when every residue class
modulo `u` has a representative that is zero or a unit. This is FC01-C08-U023.

Adapted from `is_universal_side_divisor` in `franv314/non-euclidean-pid` at
commit `087a99dc84ea7f0f70f614556f02111df63dd103`. -/
def IsUniversalSideDivisor (u : R) : Prop :=
  u ≠ 0 ∧ ¬ IsUnit u ∧
    ∀ x : R, ∃ q r : R, x = q * u + r ∧ (r = 0 ∨ IsUnit r)

/-- A Dedekind--Hasse norm is a positive domain norm for which, given nonzero
`a,b`, either `b ∣ a` or a nonzero linear combination of `a,b` has norm
strictly smaller than `N b`. This is FC01-C08-U033. -/
def IsDedekindHasseNorm (N : R → ℕ) : Prop :=
  IsPositiveDomainNorm N ∧
    ∀ a b : R, a ≠ 0 → b ≠ 0 →
      b ∣ a ∨ ∃ s t : R, 0 < N (s * a - t * b) ∧ N (s * a - t * b) < N b

end LeanCategories.Algebra

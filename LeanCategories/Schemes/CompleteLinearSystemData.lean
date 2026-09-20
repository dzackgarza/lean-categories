/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.WeilDivisorClassGroupData

/-!
# Complete linear systems of Weil divisors

Definition-level realization of Hartshorne FC06-C02-U219.

For a fixed divisor `D₀`, the complete linear system `|D₀|` is the set of
effective divisors linearly equivalent to `D₀`.

Hartshorne's further identification of this set with the projective space of
nonzero sections of `L(D₀)` modulo scalars is Proposition 7.7 / FC06-C02-U218
and is result/comparison content rather than part of this definition.
-/

@[expose] public section

namespace LeanCategories.Schemes

open AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [DivisorStandingHypothesis X]

/-- Hartshorne's complete linear system
`|D₀| = {D | D ≥ 0 and D ~ D₀}`. -/
def completeLinearSystemData (D₀ : WeilDivisor X) : Set (WeilDivisor X) :=
  {D | D.IsEffective ∧ D.LinearlyEquivalentData D₀}

end LeanCategories.Schemes

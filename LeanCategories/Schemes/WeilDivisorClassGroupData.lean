/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.PrincipalDivisorData
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Linear equivalence and the Weil divisor class group

Definition-level realization of Hartshorne FC06-C02-U157.

Linear equivalence is the relation whose difference is principal, and
`Cl X` has the corresponding quotient carrier.

The preceding principal-divisor homomorphism theorem is what proves that the
intrinsically characterized principal divisors are closed under the group
operations and that linear equivalence is an additive congruence.  Sweep III
therefore records the relation and a raw quotient carrier without selecting a
subgroup or installing the quotient-group structure before those results.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

variable {X : Scheme.{u}} [DivisorStandingHypothesis X]

/-- Hartshorne's linear equivalence relation `D ~ D'`. -/
def WeilDivisor.LinearlyEquivalentData (D E : WeilDivisor X) : Prop :=
  (D - E).IsPrincipalData

/-- Proof-free quotient carrier of Weil divisors by the source linear
equivalence relation.  Once the principal-divisor homomorphism theorem proves
that the relation is an additive congruence, this carrier acquires the source
class-group structure. -/
abbrev WeilDivisorClassCarrierData : Type _ :=
  Quot (WeilDivisor.LinearlyEquivalentData (X := X))

end LeanCategories.Schemes

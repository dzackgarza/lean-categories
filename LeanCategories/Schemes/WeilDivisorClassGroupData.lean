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

The principal divisors form an additive subgroup of `Div X`; linear
equivalence is congruence modulo that subgroup, and `Cl X` is the resulting
quotient group.

The preceding principal-divisor homomorphism theorem is what proves that the
intrinsically characterized principal divisors are closed under the group
operations.  Sweep III therefore selects the subgroup by that carrier
characterization rather than requiring a caller to provide the closure proof.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

variable {X : Scheme.{u}} [DivisorStandingHypothesis X]

/-- Predicate saying that an additive subgroup of `Div X` has exactly the
principal divisors as its elements. -/
def IsPrincipalDivisorSubgroupData (P : AddSubgroup (WeilDivisor X)) : Prop :=
  ∀ D : WeilDivisor X, D ∈ P ↔ D.IsPrincipalData

/-- The principal-divisor subgroup, selected by its intrinsic carrier.
The U156 homomorphism theorem later proves this selection satisfies the
displayed predicate. -/
def principalDivisorSubgroupData : AddSubgroup (WeilDivisor X) :=
  Classical.epsilon (IsPrincipalDivisorSubgroupData (X := X))

/-- Hartshorne's linear equivalence relation `D ~ D'`. -/
def WeilDivisor.LinearlyEquivalentData (D E : WeilDivisor X) : Prop :=
  D - E ∈ principalDivisorSubgroupData (X := X)

/-- Hartshorne's Weil divisor class group `Cl X = Div X / Prin X`. -/
abbrev WeilDivisorClassGroupData : Type _ :=
  WeilDivisor X ⧸ principalDivisorSubgroupData (X := X)

end LeanCategories.Schemes

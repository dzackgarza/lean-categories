/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.Divisors

/-!
# Principal Weil-divisor data

Definition-level realization of Hartshorne FC06-C02-U156.

For a nonzero rational function `f`, the divisor `(f)` is characterized by
the coefficient formula

`coeff_Y((f)) = ord_Y(f)`

for every prime divisor `Y`.  Hartshorne's preceding Lemma 6.1 proves these
coefficients have finite support.  Sweep III therefore records the intrinsic
coefficient predicate and the existential principal-divisor predicate without
selecting a Finsupp before that finite-support theorem is available.

The existence/specification theorem supplied by Lemma 6.1 and the assertion
that `f ↦ (f)` is a group homomorphism are result-layer facts and are not
proved here.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

variable {X : Scheme.{u}}

/-- Intrinsic coefficient characterization of the Weil divisor of a nonzero
rational function. -/
def IsDivisorOfRationalFunction [DivisorStandingHypothesis X]
    (f : X.functionFieldˣ) (D : WeilDivisor X) : Prop :=
  ∀ Y : PrimeDivisor X, D Y = X.ord (f : X.functionField) Y.genericPoint

namespace WeilDivisor

/-- A Weil divisor is principal when its coefficients are the orders of some
nonzero rational function.  This formulation does not require selecting the
Finsupp attached to a given function before U155 supplies finite support. -/
def IsPrincipalData [DivisorStandingHypothesis X] (D : WeilDivisor X) : Prop :=
  ∃ f : X.functionFieldˣ, IsDivisorOfRationalFunction f D

end WeilDivisor

end LeanCategories.Schemes

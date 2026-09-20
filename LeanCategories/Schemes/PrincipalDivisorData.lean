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
coefficients have finite support.  Sweep III therefore names the Finsupp
satisfying the intrinsic coefficient predicate by `Classical.epsilon`; it
does not ask a caller to provide finite-support evidence.

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

/-- Hartshorne's principal divisor `(f)`, selected by its coefficient
characterization.  U155 supplies the later theorem that this selection
indeed satisfies the predicate. -/
def principalDivisorData [DivisorStandingHypothesis X]
    (f : X.functionFieldˣ) : WeilDivisor X :=
  Classical.epsilon (IsDivisorOfRationalFunction f)

namespace WeilDivisor

/-- A Weil divisor is principal when it is the divisor selected from some
nonzero rational function. -/
def IsPrincipalData [DivisorStandingHypothesis X] (D : WeilDivisor X) : Prop :=
  ∃ f : X.functionFieldˣ, D = principalDivisorData f

end WeilDivisor

end LeanCategories.Schemes

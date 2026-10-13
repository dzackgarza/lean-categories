/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.CurveMorphismDegreeData
public import LeanCategories.Schemes.Divisors
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Pullback data for divisors on nonsingular curves

Definition-level realization of Hartshorne FC06-C02-U175.

For a finite morphism `f : X ⟶ Y` of nonsingular curves and a prime divisor
`Q` on `Y`, Hartshorne chooses a local parameter `t` at `Q` and defines

`f^* Q = ∑_{f(P)=Q} v_P(t) P`.

The preceding project owners already provide the codimension-one order
`Scheme.ord` and the proof-free graph of the induced function-field map.
This file records Hartshorne's coefficient formula and its linear extension
as predicates on the existing finite-support Weil-divisor carrier.

Existence of the finite-support divisor, independence of the local parameter,
and compatibility with principal divisors are propositions/results and are not
proved or selected in Sweep III.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

variable {X Y : Scheme.{u}}

/-- Intrinsic function-field characterization of a local parameter at the
generic point of a prime divisor: it has order one there. -/
def IsPrimeDivisorLocalParameterData [DivisorStandingHypothesis Y]
    (Q : PrimeDivisor Y) (t : Y.functionFieldˣ) : Prop :=
  Y.ord (t : Y.functionField) Q.genericPoint = 1

/-- Hartshorne's coefficient `v_P(t)` for the pullback of `Q`, with coefficient
zero away from the fibre over `Q`. -/
def curvePrimeDivisorPullbackCoeffData
    [DivisorStandingHypothesis X] [DivisorStandingHypothesis Y]
    (f : X ⟶ Y) [IsFinite f]
    (φ : Y.functionField ⟶ X.functionField)
    (Q : PrimeDivisor Y) (t : Y.functionFieldˣ) (P : PrimeDivisor X) : ℤ :=
  letI : DecidableEq Y := Classical.decEq Y
  if f P.genericPoint = Q.genericPoint then
    X.ord (φ.hom (t : Y.functionField)) P.genericPoint
  else 0

/-- Graph of the pullback of one prime divisor along a finite curve morphism.

The target `E` is already a `Finsupp`; hence finite support is demanded by the
result but is not proved by this declaration. -/
def IsPrimeDivisorPullbackAlongData
    [DivisorStandingHypothesis X] [DivisorStandingHypothesis Y]
    (f : X ⟶ Y) [IsFinite f]
    (φ : Y.functionField ⟶ X.functionField)
    (Q : PrimeDivisor Y) (E : WeilDivisor X) : Prop :=
  ∃ t : Y.functionFieldˣ,
    IsPrimeDivisorLocalParameterData Q t ∧
      ∀ P : PrimeDivisor X,
        E P = curvePrimeDivisorPullbackCoeffData f φ Q t P

/-- Graph of Hartshorne's pullback of an arbitrary Weil divisor, obtained by
linear extension of the prime-divisor formula.

The function-field map is constrained by the U174 graph rather than supplied
as arbitrary extension data.  No prime pullback, local parameter, or
generic-point witness is selected here. -/
def IsWeilDivisorPullbackData
    [DivisorStandingHypothesis X] [DivisorStandingHypothesis Y]
    (f : X ⟶ Y) [IsFinite f]
    (D : WeilDivisor Y) (E : WeilDivisor X) : Prop :=
  ∃ φ : Y.functionField ⟶ X.functionField,
    IsSchemeMorphismFunctionFieldPullbackData f φ ∧
      ∃ pull : PrimeDivisor Y → WeilDivisor X,
        (∀ Q, IsPrimeDivisorPullbackAlongData f φ Q (pull Q)) ∧
          E = D.sum fun Q n => n • pull Q

end LeanCategories.Schemes

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.RiemannSurfaceDivisorEvaluationData

/-!
# Divisor-representative data for the Weil pairing

Peters--Sterk FC11-C16-U036, Chapter 16, source lines 8291--8295,
defines the Weil-pairing value on chosen disjoint degree-zero divisors by

  e_k(D₁, D₂) = f₁(D₂) / f₂(D₁),  div(f_j) = k D_j.

The divisor, nonzero rational-function, principal-divisor coefficient, and
function-on-divisor evaluation owners already exist. This file only assembles
their source-specific input predicate and the displayed quotient. In
particular, evaluation uses the regular value of the meromorphic germ, not
the arbitrary point value stored in a representative. The source derives the
two cross-evaluation support conditions from disjoint divisor supports and
the principal-divisor equations; that implication is result content, so
Sweep III records the cross-evaluation conditions explicitly as input data.

The chosen functions and the disjoint representatives are explicit. Their
existence from torsion Jacobian points, moving divisors, independence of
choices, nonvanishing, the root-of-unity target, and descent to Jacobian
torsion are separate results. This is not a bundled pairing on that torsion
group. The principal-divisor equations are recorded directly as coefficient
predicates, without assuming the specification of a selected divisor.

The admitted Peters--Sterk Version JUNE 2024 PDF was re-read directly for
acceptance. Its §16.4.C clause gives exactly the displayed representative
quotient above; the immediately following prose treats nonvanishing,
root-of-unity image, and Weil-reciprocity consequences as results rather than
as part of this representative formula.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The source's chosen divisor/function presentation: the divisors have
degree zero and disjoint supports, the chosen nonzero functions have
principal divisors `k D₁` and `k D₂`, and both cross-evaluations satisfy
the existing divisor-evaluation admissibility predicate.

No existence or equivalence with the Jacobian torsion condition is asserted.
The source proves the two cross-evaluation conditions from the preceding
data; requiring them here keeps that proof out of the construction. The level
enters the principal-divisor equations, not the value formula. -/
def CurveWeilPairingAdmissibleData (k : ℕ)
    (D₁ D₂ : CurveDivisorData X)
    (f₁ f₂ : NonzeroCurveRationalFunctionData X) : Prop :=
  curveDivisorDegreeData X D₁ = 0 ∧
    curveDivisorDegreeData X D₂ = 0 ∧
    IsCurvePrincipalDivisorData f₁ (k • D₁) ∧
    IsCurvePrincipalDivisorData f₂ (k • D₂) ∧
    Disjoint (curveDivisorSupportData D₁) (curveDivisorSupportData D₂) ∧
    CurveDivisorEvaluationAdmissibleData f₁ D₂ ∧
    CurveDivisorEvaluationAdmissibleData f₂ D₁

/-- The displayed representative formula, computed from the existing
finite-product evaluation. Total complex division does not assert that
the denominator is nonzero for arbitrary input data. -/
def curveWeilPairingRepresentativeData
    (D₁ D₂ : CurveDivisorData X)
    (f₁ f₂ : NonzeroCurveRationalFunctionData X) : ℂ :=
  curveDivisorEvaluationComplexData f₁ D₂ /
    curveDivisorEvaluationComplexData f₂ D₁

end LeanCategories.Algebra

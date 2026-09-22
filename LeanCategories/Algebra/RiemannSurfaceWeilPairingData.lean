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
the arbitrary point value stored in a representative.

The chosen functions and the disjoint representatives are explicit. Their
existence from torsion Jacobian points, moving divisors, independence of
choices, nonvanishing, the root-of-unity target, and descent to Jacobian
torsion are separate results. This is not a bundled pairing on that torsion
group. The principal-divisor equations are recorded directly as coefficient
predicates, without assuming the specification of a selected divisor.

The original June-2024 extraction is unavailable on this host. The indexed
source clause and the existing U024/U025 owners are the transcription
inputs; complete original-prose acceptance remains open.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The source's chosen divisor/function presentation: the divisors have
degree zero and disjoint supports, and the chosen nonzero functions have
principal divisors `k D₁` and `k D₂`.

No existence or equivalence with the Jacobian torsion condition is asserted.
The level enters these principal-divisor equations, not the value formula. -/
def CurveWeilPairingAdmissibleData (k : ℕ)
    (D₁ D₂ : CurveDivisorData X)
    (f₁ f₂ : NonzeroCurveRationalFunctionData X) : Prop :=
  curveDivisorDegreeData X D₁ = 0 ∧
    curveDivisorDegreeData X D₂ = 0 ∧
    IsCurvePrincipalDivisorData f₁ (k • D₁) ∧
    IsCurvePrincipalDivisorData f₂ (k • D₂) ∧
    Disjoint (curveDivisorSupportData D₁) (curveDivisorSupportData D₂)

/-- The displayed representative formula, computed from the existing
finite-product evaluation. Total complex division does not assert that
the denominator is nonzero for arbitrary input data. -/
def curveWeilPairingRepresentativeData
    (D₁ D₂ : CurveDivisorData X)
    (f₁ f₂ : NonzeroCurveRationalFunctionData X) : ℂ :=
  curveDivisorEvaluationComplexData f₁ D₂ /
    curveDivisorEvaluationComplexData f₂ D₁

/-- The source-restricted representative value at torsion level `k`.

Only the defining hypotheses are supplied. No proof of the cross-support
conditions, nonvanishing, or descent is required to record this formula. -/
def curveWeilPairingData (k : ℕ)
    (D₁ D₂ : CurveDivisorData X)
    (f₁ f₂ : NonzeroCurveRationalFunctionData X)
    (_source : CurveWeilPairingAdmissibleData k D₁ D₂ f₁ f₂) : ℂ :=
  curveWeilPairingRepresentativeData D₁ D₂ f₁ f₂

end LeanCategories.Algebra

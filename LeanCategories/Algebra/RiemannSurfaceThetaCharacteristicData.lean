/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.RiemannSurfaceAbelJacobiData
public import LeanCategories.Algebra.RiemannSurfaceCanonicalDivisorData

/-!
# Theta characteristics and Riemann-constant data

Preparatory data for Peters--Sterk FC11-C16-U030: a half-canonical divisor,
or theta characteristic, is a divisor `θ` with `2θ` linearly equivalent
to a certified canonical-divisor representative.

This is a thin predicate over the existing divisor and linear-equivalence
owners. Existence of a canonical divisor and of a half-canonical divisor,
their degree statements, and translation properties are results.

For the Riemann constant, the divisor-class extension of Abel--Jacobi is
recorded by an exact graph on a finite divisor representative. Pointwise
path-integral functionals are summed through the native free-abelian-group
lift and then sent to the raw Jacobian quotient. Path independence,
linear-equivalence descent, existence, uniqueness, and functionality are
result-layer facts.

The causal reference owners are LeanPool at
3fc79f0a795f19fffcc59eee3efaf5faa52de3c3 and jacobian-challenge at
8ce1ec28aed1c78b3b39d0bae26e2858c82f5143, both Apache-2.0.
No such result is proved or inserted as a structure field here.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff

namespace LeanCategories.Algebra

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The defining half-canonical condition `2θ ∼ K_C`, retaining the
chosen nonzero form which specifies the canonical-divisor representative. -/
def IsCurveThetaCharacteristicData {form : CurveHolomorphicOneFormData X}
    {hform : form ≠ 0} (K : CurveCanonicalDivisorData form hform)
    (θ : CurveDivisorData X) : Prop :=
  (2 • θ).LinearlyEquivalentData K.val

/-- Divisor representatives satisfying the source's half-canonical
condition. No existence of a member is asserted. -/
abbrev CurveThetaCharacteristicData {form : CurveHolomorphicOneFormData X}
    {hform : form ≠ 0} (K : CurveCanonicalDivisorData form hform) :=
  {θ : CurveDivisorData X // IsCurveThetaCharacteristicData K θ}

/-- Peters--Sterk's Riemann constant associated to a supplied theta
characteristic representative: `κ = α([θ₀])`.

This is a graph predicate, not a selected value. Its independence of the
divisor representative and of all chosen paths belongs to Sweep IV. -/
def IsCurveRiemannConstantData (x₀ : X)
    {form : CurveHolomorphicOneFormData X} {hform : form ≠ 0}
    {K : CurveCanonicalDivisorData form hform}
    (θ₀ : CurveThetaCharacteristicData K)
    (κ : CurveJacobianQuotientData X x₀) : Prop :=
  IsCurveDivisorAbelJacobiClassData x₀ θ₀.1 κ

end LeanCategories.Algebra

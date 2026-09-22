/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.RiemannSurfaceCanonicalDivisorData
public import LeanCategories.Algebra.RiemannSurfaceAbelJacobiData

/-!
# Theta characteristics and Riemann-constant data

Peters--Sterk FC11-C16-U030: a half-canonical divisor, or theta
characteristic, is a divisor `θ` with `2θ` linearly equivalent to the
canonical divisor. For the chosen `θ₀`, the Riemann constant is `α([θ₀])`.

These are thin constructions over the existing divisor, linear-equivalence,
canonical-divisor, and based Abel--Jacobi owners. The point map extends to
finite integral divisors using native `FreeAbelianGroup.lift`; it is not an
arbitrary homomorphism supplied as new input. This fixes the same basepoint
normalization in every degree. Descent to divisor classes, existence of a
half-canonical divisor, its degree, and translation properties are results,
not constructor obligations here. The choice of `θ₀` remains explicit.

The causal reference owners are LeanPool at
3fc79f0a795f19fffcc59eee3efaf5faa52de3c3 and jacobian-challenge at
8ce1ec28aed1c78b3b39d0bae26e2858c82f5143, both Apache-2.0.
Complete original-prose acceptance and target-pin validation remain open.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff

namespace LeanCategories.Algebra

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The defining half-canonical condition `2θ ∼ K_C`, retaining the
chosen nonzero form which specifies the canonical-divisor representative. -/
def IsCurveThetaCharacteristicData (form : CurveHolomorphicOneFormData X)
    (hform : form ≠ 0) (θ : CurveDivisorData X) : Prop :=
  (2 • θ).LinearlyEquivalentData (curveCanonicalDivisorData form hform)

/-- Divisor representatives satisfying the source's half-canonical
condition. No existence of a member is asserted. -/
abbrev CurveThetaCharacteristicData (form : CurveHolomorphicOneFormData X)
    (hform : form ≠ 0) :=
  {θ : CurveDivisorData X // IsCurveThetaCharacteristicData form hform θ}

/-- Riemann-constant data for the specified half-canonical divisor
and the specified Abel--Jacobi basepoint. Class descent is not asserted. -/
def curveRiemannConstantData (x₀ : X) (form : CurveHolomorphicOneFormData X)
    (hform : form ≠ 0) (θ₀ : CurveThetaCharacteristicData form hform) :
    CurveJacobianData X :=
  curveDivisorAbelJacobiData X x₀ θ₀.val

end LeanCategories.Algebra

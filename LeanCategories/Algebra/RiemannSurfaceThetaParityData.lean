/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.RiemannSurfaceLinearSystemData
public import LeanCategories.Algebra.RiemannSurfaceThetaCharacteristicData
public import Mathlib.Algebra.Ring.Parity

/-!
# Parity of theta characteristics

Preparatory data for Peters--Sterk FC11-C16-U031. Once the source
Riemann--Roch subspace `L(θ)` has been constructed, parity is the parity of
its dimension. Sweep III does not select that subspace before closure/existence
has been proved.

The input is a divisor representative satisfying the half-canonical predicate
and a certified linear-system carrier. This file deliberately does not claim
the intrinsic U031 predicate until the canonical `L(θ)` construction is
available. Class invariance, theta-function multiplicity, quadratic refinement,
and counting statements remain result content.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff

namespace LeanCategories.Algebra.CurveThetaCharacteristicData

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]
  {form : CurveHolomorphicOneFormData X} {hform : form ≠ 0}
  {K : CurveCanonicalDivisorData form hform}

/-- Relative parity predicate for a certified linear-system carrier. -/
def IsEvenForLinearSystemData (θ : CurveThetaCharacteristicData K)
    (L : CurveLinearSystemData θ.val) : Prop :=
  Even (curveSectionDimensionData L)

/-- Relative odd-parity predicate for a certified linear-system carrier. -/
def IsOddForLinearSystemData (θ : CurveThetaCharacteristicData K)
    (L : CurveLinearSystemData θ.val) : Prop :=
  Odd (curveSectionDimensionData L)

end LeanCategories.Algebra.CurveThetaCharacteristicData

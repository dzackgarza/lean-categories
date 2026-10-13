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

Definition-level data for Peters--Sterk FC11-C16-U031. Parity is the parity of
the dimension of the source Riemann--Roch space `L(θ)`.

The input is a divisor representative satisfying the half-canonical predicate
and, for the relative predicates, a certified linear-system carrier. The
intrinsic predicates quantify over such a carrier with the exact source
membership condition rather than selecting one. Thus closure/existence of
`L(θ)` is not proved or installed as data. Class invariance, theta-function
multiplicity, quadratic refinement, and counting statements remain result
content.
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

/-- A theta characteristic is even when its source Riemann--Roch space has
even dimension.

The existential witness is required to have exactly the canonical source
carrier. No linear-system submodule is selected by this definition. -/
def IsEvenData (θ : CurveThetaCharacteristicData K) : Prop :=
  ∃ L : CurveLinearSystemData θ.val,
    IsEvenForLinearSystemData θ L

/-- A theta characteristic is odd when its source Riemann--Roch space has odd
dimension, again without selecting the canonical submodule. -/
def IsOddData (θ : CurveThetaCharacteristicData K) : Prop :=
  ∃ L : CurveLinearSystemData θ.val,
    IsOddForLinearSystemData θ L

end LeanCategories.Algebra.CurveThetaCharacteristicData

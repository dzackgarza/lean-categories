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

Peters--Sterk FC11-C16-U031 calls a theta characteristic even or odd
according to the parity of `h⁰(C,θ)`. The dimension is constructed by the
mapped LeanPool `RS.LinSys`/`RS.l` adaptation, not supplied as a number,
an arbitrary space, or a parity assignment.

The input is a divisor representative already satisfying the U030
half-canonical predicate. Class invariance, the comparison with theta-function
multiplicity, the quadratic-refinement interpretation and counting results
are not part of these definitions.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff

namespace LeanCategories.Algebra.CurveThetaCharacteristicData

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  {form : CurveHolomorphicOneFormData X} {hform : form ≠ 0}

/-- An even theta characteristic has an even-dimensional Riemann--Roch space. -/
def IsEvenData (θ : CurveThetaCharacteristicData form hform) : Prop :=
  Even (curveSectionDimensionData θ.val)

/-- An odd theta characteristic has an odd-dimensional Riemann--Roch space. -/
def IsOddData (θ : CurveThetaCharacteristicData form hform) : Prop :=
  Odd (curveSectionDimensionData θ.val)

end LeanCategories.Algebra.CurveThetaCharacteristicData

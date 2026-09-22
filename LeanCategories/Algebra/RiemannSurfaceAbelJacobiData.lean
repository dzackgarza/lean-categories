/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Definition-level adaptation of mrdouglasny/jacobian-challenge, Apache-2.0,
revision 8ce1ec28aed1c78b3b39d0bae26e2858c82f5143.
-/
module

public import LeanCategories.Algebra.RiemannSurfaceJacobianQuotientData

/-!
# Abel--Jacobi map data for a compact complex curve

Peters--Sterk FC11-C16-U029, adapted from the pinned reference's
`Jacobians/Axioms/AbelJacobiMap.lean::{pathIntegralBasepointFunctional,
ofCurveAmbient,ofCurveImpl}`. The intrinsic dual replaces its coordinate
basis. Its basepoint normalization and integral-period quotient are retained.

The scalar integral, analytic arcs, complex dual, and period quotient reuse
existing owners. The endpoint condition and integral equation specify a lift
along one arc: different paths need not agree before taking the quotient.
Existence, selection specifications, path/basepoint independence, and
holomorphy remain result obligations, not assumptions or proofs here.
Complete original-prose acceptance remains open.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff

namespace LeanCategories.Algebra

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The integral equation for a dual vector along an explicit analytic
arc. Linearity of the scalar integral is a separate result. -/
def IsCurveArcIntegralFunctionalData (γ : CurveAnalyticArcData X)
    (φ : CurveJacobianDualData X) : Prop :=
  ∀ form : CurveHolomorphicOneFormData X,
    φ form = curveCanonicalArcIntegralData γ form

/-- A path-integral lift is computed along one analytic arc with the
specified endpoints. Different arcs need not give the same lift. -/
def IsCurvePathIntegralFunctionalData (x₀ x : X)
    (φ : CurveJacobianDualData X) : Prop :=
  ∃ γ : CurveAnalyticArcData X,
    γ.extend 0 = x₀ ∧ γ.extend 1 = x ∧
      IsCurveArcIntegralFunctionalData γ φ

/-- A path-integral lift selected by the endpoint and integral equations.
Its specification, including existence, is not asserted by this definition. -/
def curvePathIntegralFunctionalData (x₀ x : X) : CurveJacobianDualData X :=
  Classical.epsilon (IsCurvePathIntegralFunctionalData x₀ x)

/-- The reference's basepoint-normalized lift, before taking its class
modulo integral periods. No global primitive of a one-form is asserted. -/
def curveAbelJacobiLiftData (x₀ x : X) : CurveJacobianDualData X :=
  curvePathIntegralFunctionalData x₀ x - curvePathIntegralFunctionalData x₀ x₀

/-- Abel--Jacobi map data into the period quotient whose homology
basepoint is explicitly `x₀`. This avoids assuming basepoint independence. -/
def curveAbelJacobiMapData (x₀ : X) (x : X) :
    CurveJacobianPeriodQuotientData X x₀ :=
  curveJacobianPeriodClassData X x₀ (curveAbelJacobiLiftData x₀ x)

/-- The compact-curve specialization with the reference's fixed
homology-basepoint convention for the Jacobian carrier. Independence of
that convention and of the selected integration paths remains result content. -/
def curveAbelJacobiData (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (x : X) : CurveJacobianData X :=
  curveJacobianPeriodClassData X (Classical.arbitrary X)
    (curveAbelJacobiLiftData x₀ x)

end LeanCategories.Algebra

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Definition-level adaptation of mrdouglasny/jacobian-challenge, Apache-2.0,
revision 8ce1ec28aed1c78b3b39d0bae26e2858c82f5143.
-/
module

public import LeanCategories.Algebra.RiemannSurfaceDivisorData
public import LeanCategories.Algebra.RiemannSurfaceJacobianQuotientData

/-!
# Abel--Jacobi map data for a compact complex curve

Preparatory data for Peters--Sterk FC11-C16-U029, compared with the pinned reference's
`Jacobians/Axioms/AbelJacobiMap.lean::{pathIntegralBasepointFunctional,
ofCurveAmbient,ofCurveImpl}`. The intrinsic dual replaces its coordinate
basis. Its basepoint normalization and integral-period quotient are retained.

The pinned reference constructs its single-form path-integral `LinearMap` by
proving additivity and scalar compatibility. Those are result-layer facts.
Sweep III therefore does not select a dual-valued path integral or a function
from the curve to the Jacobian.

Instead, after the raw Jacobian quotient is available, this file records the
source map by its exact graph: a quotient class is related to a point when it
has a representative dual functional whose values are the path integrals from
the basepoint to that point. Existence, path independence, uniqueness, and
functionality of this graph remain result-layer statements.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff

namespace LeanCategories.Algebra

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The integral equation that a future dual-valued path integral must satisfy
along an explicit analytic arc. Linearity is a separate result. -/
def IsCurveArcIntegralFunctionalData (γ : CurveAnalyticArcData X)
    (φ : CurveJacobianDualData X) : Prop :=
  ∀ form : CurveHolomorphicOneFormData X,
    φ form = curveCanonicalArcIntegralData γ form

/-- Candidate dual-valued path-integral lift with the specified endpoints.
Existence is not asserted. -/
def IsCurvePathIntegralFunctionalData (x₀ x : X)
    (φ : CurveJacobianDualData X) : Prop :=
  ∃ γ : CurveAnalyticArcData X,
    γ.extend 0 = x₀ ∧ γ.extend 1 = x ∧
      IsCurveArcIntegralFunctionalData γ φ

/-- An explicit analytic arc with prescribed endpoints. Supplying such an arc
does not assert that every pair of points admits one. -/
structure CurveBasedAnalyticArcData (x₀ x : X) where
  arc : CurveAnalyticArcData X
  start_eq : arc.extend 0 = x₀
  end_eq : arc.extend 1 = x

/-- Raw single-form path integral along a supplied endpoint-constrained arc.
This is deliberately a plain function rather than a `LinearMap`. -/
def curvePathIntegralFunctionData {x₀ x : X}
    (γ : CurveBasedAnalyticArcData x₀ x) :
    CurveHolomorphicOneFormData X → ℂ :=
  fun form => curveCanonicalArcIntegralData γ.arc form

/-- Raw basepoint-normalized integral function for two supplied arcs.
Upgrading this to the numerator of the Abel--Jacobi quotient requires the
linearity result deferred to Sweep IV. -/
def curveAbelJacobiLiftFunctionData {x₀ x : X}
    (γ : CurveBasedAnalyticArcData x₀ x)
    (γ₀ : CurveBasedAnalyticArcData x₀ x₀) :
    CurveHolomorphicOneFormData X → ℂ :=
  fun form =>
    curvePathIntegralFunctionData γ form -
      curvePathIntegralFunctionData γ₀ form

/-- Exact graph of the Abel--Jacobi construction at a point.

The quotient class `q` represents the source value `α(x)` precisely when it
has a dual-functional representative given by integration along an analytic
arc from the fixed basepoint `x₀` to `x`. No such representative is selected
here. -/
def IsCurveAbelJacobiClassData (x₀ x : X)
    (q : CurveJacobianQuotientData X x₀) : Prop :=
  ∃ φ : CurveJacobianDualData X,
    IsCurvePathIntegralFunctionalData x₀ x φ ∧
      curveJacobianClassData X x₀ φ = q

/-- Graph predicate for a proposed Abel--Jacobi function.

This does not assert that such a function exists. Once Sweep IV proves the
pointwise graph is inhabited and single-valued, the source Abel--Jacobi map is
the unique function satisfying this predicate. -/
def IsCurveAbelJacobiMapData (x₀ : X)
    (α : X → CurveJacobianQuotientData X x₀) : Prop :=
  ∀ x, IsCurveAbelJacobiClassData x₀ x (α x)

/-- Additive extension of pointwise dual functionals from points of the curve
to finite integral divisors. -/
def curveDivisorAbelJacobiLiftData
    (φ : X → CurveJacobianDualData X) :
    CurveDivisorData X →+ CurveJacobianDualData X :=
  FreeAbelianGroup.lift φ

/-- Exact graph of Abel--Jacobi on a divisor representative.

Only points in the finite support of `D` are required to carry the source
path-integral functional. Values of `φ` away from the support are irrelevant
to the resulting free-abelian-group sum. -/
def IsCurveDivisorAbelJacobiClassData (x₀ : X)
    (D : CurveDivisorData X)
    (q : CurveJacobianQuotientData X x₀) : Prop :=
  ∃ φ : X → CurveJacobianDualData X,
    (∀ x ∈ curveDivisorSupportData D,
      IsCurvePathIntegralFunctionalData x₀ x (φ x)) ∧
    curveJacobianClassData X x₀ (curveDivisorAbelJacobiLiftData φ D) = q

end LeanCategories.Algebra

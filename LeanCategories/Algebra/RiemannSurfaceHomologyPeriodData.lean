/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Definition-level adaptation of mrdouglasny/jacobian-challenge, Apache-2.0,
revision 8ce1ec28aed1c78b3b39d0bae26e2858c82f5143.
-/
module

public import LeanCategories.Algebra.RiemannSurfacePeriodIntegralData
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Homology-level period data

Supporting definitions for Peters--Sterk FC11-C16-U026. The homology carrier
and loop-class map reuse the exact native owners used by the pinned reference's
`RiemannSurface/Homology.lean` and `Axioms/PeriodCycleBasis.lean`.

The scalar integral already lives at the analytic-arc owner. A functional on a
homology class is specified by its values on every analytic loop representing
that class, then selected by that intrinsic equation. This is the same
definition-only selection boundary used for principal divisors elsewhere in
this corpus: no representative is supplied in place of a homology class, and
no unspecified functional is an input.

Representability by analytic loops, linearity, homotopy invariance, existence
and uniqueness of the selected functional, its specification, and additivity
in homology are result content. None is assumed as a new axiom or proved here.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff

namespace LeanCategories.Algebra

universe u

/-- The reference's first integral homology carrier: the additive form of
the abelianization of the based fundamental group. -/
abbrev CurveIntegralFirstHomologyData (X : Type u) [TopologicalSpace X] (x₀ : X) :=
  Additive (Abelianization (FundamentalGroup X x₀))

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- Underlying native path of the reference's analytic-loop data.
Continuity is carried by the existing data and native restriction; the
endpoint fields are exactly the supplied endpoint equations. -/
def curveAnalyticLoopPathData {x₀ : X} (γ : CurveAnalyticLoopData x₀) :
    Path x₀ x₀ where
  toContinuousMap :=
    (⟨γ.arc.extend, γ.arc.continuous'⟩ : C(ℝ, X)).restrict (Set.Icc (0 : ℝ) 1)
  source' := γ.start_eq
  target' := γ.end_eq

/-- The native homotopy-class and abelianization maps applied to an
analytic loop, matching the pinned `loopToHomology` construction. -/
def curveAnalyticLoopHomologyClassData {x₀ : X} (γ : CurveAnalyticLoopData x₀) :
    CurveIntegralFirstHomologyData X x₀ :=
  Additive.ofMul (Abelianization.of
    (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (curveAnalyticLoopPathData γ))))

/-- Defining period equation on every analytic-loop representative of a
homology class. This records the whole graph condition, not a selected
representative or an unconstrained element of the dual. -/
def IsCurveHomologyPeriodFunctionalData {x₀ : X}
    (h : CurveIntegralFirstHomologyData X x₀)
    (φ : CurveJacobianDualData X) : Prop :=
  ∀ γ : CurveAnalyticLoopData x₀, curveAnalyticLoopHomologyClassData γ = h →
    ∀ form : CurveHolomorphicOneFormData X,
      φ form = curveCanonicalArcIntegralData γ.arc form

/-- The raw homology-to-dual period map selected by the source integral
equation. Its specification and homomorphism laws are deliberately not
asserted by this definition. -/
def curveHomologyPeriodFunctionalData {x₀ : X}
    (h : CurveIntegralFirstHomologyData X x₀) : CurveJacobianDualData X :=
  Classical.epsilon (IsCurveHomologyPeriodFunctionalData h)

end LeanCategories.Algebra

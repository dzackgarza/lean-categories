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

The scalar integral already lives at the analytic-arc owner. A candidate
functional on a homology class is specified by its values on every analytic
loop representing that class. Sweep III does not select such a functional:
existence and linearity are exactly the result-layer facts needed before the
source period map can be constructed.

Representability by analytic loops, linearity, homotopy invariance, existence,
uniqueness, and additivity in homology are result content. None is assumed as
a new axiom or used here to manufacture a value.
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

/-- Candidate period functionals arising from some integral homology class.
This is only a set until existence/uniqueness and additivity of the period
functional are established in the result layer. -/
def curveIntegralPeriodCandidateSetData {x₀ : X} :
    Set (CurveJacobianDualData X) :=
  {φ | ∃ h : CurveIntegralFirstHomologyData X x₀,
    IsCurveHomologyPeriodFunctionalData h φ}

end LeanCategories.Algebra

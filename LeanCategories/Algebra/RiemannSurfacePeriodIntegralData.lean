/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Definition-level adaptation of mrdouglasny/jacobian-challenge, Apache-2.0,
revision 8ce1ec28aed1c78b3b39d0bae26e2858c82f5143.
-/
module

public import LeanCategories.Algebra.RiemannSurfaceJacobianData
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Period-integral data on Riemann surfaces

Supporting definitions for Peters--Sterk FC11-C16-U026, extracted from the
pinned reference's `RiemannSurface/{AnalyticArc,MultiChartIntegral,
PartitionIndependence,CanonicalArcIntegral}.lean`.

The reference's analytic-arc and chart-subordinate-partition data are retained.
Its chart coefficients are obtained from the native cotangent section by
pulling back along the inverse chart, instead of introducing another space of
one-forms. Segment integrals, their finite sum, and the moving-chart integral
are the reference's literal formulas using native derivatives and integration.

No arc or partition existence, integrability, chart/partition independence,
linearity, homotopy invariance, homology descent, or period-lattice theorem is
proved. In particular, the scalar integral is not presented as an already
constructed element of the complex dual or as a homology-level period map.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff BigOperators

namespace LeanCategories.Algebra

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- Strong piecewise analyticity from the pinned `IsAnalyticArcStrong`:
every base cell admits a finite chartwise analytic refinement extending
past each closed refined cell. No analyticity is imposed across corners. -/
def IsCurveAnalyticArcStrongData (extend : ℝ → X)
    (basePartition : Finset ℝ) : Prop :=
  ∀ a ∈ basePartition, ∀ b ∈ basePartition, a < b →
    (∀ r ∈ basePartition, r ∉ Set.Ioo a b) →
      ∃ τ : Finset ℝ, a ∈ τ ∧ b ∈ τ ∧ (↑τ ⊆ Set.Icc a b) ∧
        ∀ s ∈ τ, ∀ t ∈ τ, s < t → (∀ r ∈ τ, r ∉ Set.Ioo s t) →
          ∃ (p : X) (U : Set ℝ) (f : ℝ → ℂ),
            IsOpen U ∧ Set.Icc s t ⊆ U ∧ AnalyticOnNhd ℝ f U ∧
            (∀ r ∈ U ∩ Set.Icc a b,
              extend r ∈ (extChartAt 𝓘(ℂ) p).source) ∧
            (∀ r ∈ U ∩ Set.Icc a b,
              (extChartAt 𝓘(ℂ) p) (extend r) = f r)

/-- The pinned reference's piecewise-real-analytic arc data. Only the
restriction of `extend` to `[0,1]` enters the integral formulas. -/
structure CurveAnalyticArcData (X : Type u) [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] where
  extend : ℝ → X
  continuous' : Continuous extend
  partition : Finset ℝ
  partition_subset : ↑partition ⊆ Set.Icc (0 : ℝ) 1
  zero_mem : (0 : ℝ) ∈ partition
  one_mem : (1 : ℝ) ∈ partition
  is_analytic_strong : IsCurveAnalyticArcStrongData extend partition

/-- Analytic loop data with both endpoints at the specified basepoint. -/
structure CurveAnalyticLoopData (x₀ : X) where
  arc : CurveAnalyticArcData X
  start_eq : arc.extend 0 = x₀
  end_eq : arc.extend 1 = x₀

/-- Coefficient of the pullback of an intrinsic one-form by the inverse
chart, evaluated on the coordinate tangent vector `1`. Only values in the
chart target are used by chart-subordinate integration. -/
def curveOneFormChartCoefficientData (form : CurveHolomorphicOneFormData X)
    (p : X) (z : ℂ) : ℂ :=
  form ((extChartAt 𝓘(ℂ) p).symm z)
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) p).symm z
      ((NormedSpace.fromTangentSpace (𝕜 := ℂ) z).symm 1))

/-- Raw integral of a chart expression over a segment. Chart containment
is recorded separately by `CurveChartSubordinatePartitionData`. -/
def curvePathIntegralOnChartSegmentData (γ : CurveAnalyticArcData X)
    (p : X) (a b : ℝ) (form : CurveHolomorphicOneFormData X) : ℂ :=
  ∫ r in a..b,
    curveOneFormChartCoefficientData form p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
      derivWithin (fun s : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend s))
        (Set.Ioo a b) r

/-- Finite partition of `[0,1]` with a chart containing the image of
each entire closed cell, as in the pinned `ChartSubordinatePartition`. -/
structure CurveChartSubordinatePartitionData (γ : CurveAnalyticArcData X) where
  n : ℕ
  t : Fin (n + 1) → ℝ
  p : Fin n → X
  t_zero : t 0 = 0
  t_last : t (Fin.last n) = 1
  t_mono : Monotone t
  mem_source : ∀ i : Fin n, ∀ s ∈ Set.Icc (t i.castSucc) (t i.succ),
    γ.extend s ∈ (chartAt ℂ (p i)).source

/-- Multi-chart integral for an explicit subordinate partition. The
partition is not replaced by a global single-chart assumption. -/
def curvePathIntegralOverPartitionData (γ : CurveAnalyticArcData X)
    (P : CurveChartSubordinatePartitionData γ)
    (form : CurveHolomorphicOneFormData X) : ℂ :=
  ∑ i : Fin P.n,
    curvePathIntegralOnChartSegmentData γ (P.p i) (P.t i.castSucc) (P.t i.succ) form

/-- The pinned moving-chart integrand. The chart center is fixed at
`γ(r)` while differentiating in the separate parameter `s`. -/
def curveCanonicalPeriodIntegrandData (γ : CurveAnalyticArcData X)
    (form : CurveHolomorphicOneFormData X) (r : ℝ) : ℂ :=
  curveOneFormChartCoefficientData form (γ.extend r)
      ((extChartAt 𝓘(ℂ) (γ.extend r)) (γ.extend r)) *
    deriv (fun s : ℝ => (extChartAt 𝓘(ℂ) (γ.extend r)) (γ.extend s)) r

/-- Scalar period integral along an analytic arc, without a chosen
chart partition. Its comparison with the partitioned formula is a result,
not a constructor argument. -/
def curveCanonicalArcIntegralData (γ : CurveAnalyticArcData X)
    (form : CurveHolomorphicOneFormData X) : ℂ :=
  ∫ r in (0 : ℝ)..1, curveCanonicalPeriodIntegrandData γ form r

end LeanCategories.Algebra

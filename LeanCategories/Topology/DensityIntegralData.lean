/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Real.Basic

/-!
# Integration data for densities on manifolds

Definition-level realization of Lee FC08-C16-U062.

For a density supported in one coordinate chart, Lee defines its integral by
pulling the density back along the inverse chart and applying the Euclidean
density integral.  An arbitrary compactly supported density is localized by a
subordinate partition of unity and the chart-supported values are summed.

As with FC08-C16-U031, independence of the chart and partition is theorem-layer
well-definedness.  Sweep III therefore records the local formula and the exact
graph over every supplied valid partition presentation; it does not select one
preferred partition.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

universe u v w

/-- Lee's integral of a density supported in one chart: pull back by the inverse
chart and apply the Euclidean density integral. -/
def densitySingleChartIntegral
    {ChartDensity : Type u} {EuclideanDensity : Type v}
    (pullbackByChartInverse : ChartDensity → EuclideanDensity)
    (euclideanDensityIntegral : EuclideanDensity → ℝ)
    (μ : ChartDensity) : ℝ :=
  euclideanDensityIntegral (pullbackByChartInverse μ)

/-- Valid partition-of-unity presentation data for compactly supported
densities.

`Presentation μ` is supplied by the ambient manifold/partition owner and is
intended to be the type of Lee-valid subordinate chart presentations of `μ`.
`pieces μ P` lists the finitely many nonzero localized densities `ψ_i μ`.
No existence or compatibility theorem is bundled into this data record. -/
structure DensityIntegralPresentationData
    (Density : Type u) (ChartDensity : Type v) where
  Presentation : Density → Type w
  pieces : ∀ μ, Presentation μ → List ChartDensity

/-- Scalar attached to one supplied valid density presentation. -/
def densityPresentationIntegral
    {Density : Type u} {ChartDensity : Type v}
    (D : DensityIntegralPresentationData.{u, v, w} Density ChartDensity)
    (localIntegral : ChartDensity → ℝ)
    (μ : Density) (P : D.Presentation μ) : ℝ :=
  (D.pieces μ P).map localIntegral |>.sum

/-- Exact all-presentations graph for Lee's manifold density integral.

The omitted theorem that chart/partition choices do not matter is precisely
what makes this graph consistent. -/
def IsManifoldDensityIntegralData
    {Density : Type u} {ChartDensity : Type v}
    (D : DensityIntegralPresentationData.{u, v, w} Density ChartDensity)
    (localIntegral : ChartDensity → ℝ)
    (integral : Density → ℝ) : Prop :=
  ∀ (μ : Density) (P : D.Presentation μ),
    integral μ = densityPresentationIntegral D localIntegral μ P

/-- Source-faithful manifold density-integral data: a functional together with
Lee's exact graph over every valid partition presentation.

Presentation existence and choice-independence supply existence later; no
arbitrary functional is selected before those results. -/
abbrev ManifoldDensityIntegralData
    {Density : Type u} {ChartDensity : Type v}
    (D : DensityIntegralPresentationData.{u, v, w} Density ChartDensity)
    (localIntegral : ChartDensity → ℝ) :=
  {integral : Density → ℝ //
    IsManifoldDensityIntegralData D localIntegral integral}

end LeanCategories.Topology

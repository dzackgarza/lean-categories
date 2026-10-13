/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Real.Basic

/-!
# Riemannian integration formulas

Definition-level realization of Lee FC08-C16-U037.

For an oriented Riemannian manifold, Lee defines integration of a compactly
supported continuous function by multiplying it with the Riemannian volume
form and applying the already-defined integral of top forms.  On a compact
manifold, the volume is the integral of the volume form itself.

The geometric owners of the Riemannian volume form and of top-form integration
are deliberately supplied as parameters.  Sweep III records only Lee's two
formulas; chart/partition invariance and construction of those owners remain
result-layer work.
-/

@[expose] public section

namespace LeanCategories.Topology

/-- Lee's integral of a compactly supported continuous function against the
Riemannian volume form.

The type `CompactlySupportedContinuousFunction` is supplied by the ambient
manifold integration owner, so its elements already carry the source's support
and continuity hypotheses. -/
def riemannianFunctionIntegral
    {RiemannianMetric CompactlySupportedContinuousFunction TopForm : Type*}
    (volumeForm : RiemannianMetric → TopForm)
    (functionTimesForm : CompactlySupportedContinuousFunction → TopForm → TopForm)
    (integralTopForm : TopForm → ℝ)
    (g : RiemannianMetric)
    (f : CompactlySupportedContinuousFunction) : ℝ :=
  integralTopForm (functionTimesForm f (volumeForm g))

/-- Lee's volume of a compact oriented Riemannian manifold: integrate its
Riemannian volume form.

Compactness is the source hypothesis ensuring that the volume form is in the
domain of the supplied top-form integral; it is not proved or encoded here. -/
def riemannianVolume
    {RiemannianMetric TopForm : Type*}
    (volumeForm : RiemannianMetric → TopForm)
    (integralTopForm : TopForm → ℝ)
    (g : RiemannianMetric) : ℝ :=
  integralTopForm (volumeForm g)

/-- The orientation-free version of Lee's Riemannian function integral, using
the Riemannian density instead of the oriented volume form.

The notation `dV_g` in FC08-C16-U065 names `riemannianDensity g`; this function
records the displayed integral formula and no comparison with the oriented
volume-form presentation. -/
def riemannianDensityFunctionIntegral
    {RiemannianMetric CompactlySupportedContinuousFunction Density : Type*}
    (riemannianDensity : RiemannianMetric → Density)
    (functionTimesDensity : CompactlySupportedContinuousFunction → Density → Density)
    (integralDensity : Density → ℝ)
    (g : RiemannianMetric)
    (f : CompactlySupportedContinuousFunction) : ℝ :=
  integralDensity (functionTimesDensity f (riemannianDensity g))

end LeanCategories.Topology

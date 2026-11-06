/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.InvariantIntegralCurve

/-! # Card: `LeanCategories.Topology.isMIntegralCurve_mulInvariantIntegralCurveData`

source: Lee, *Introduction to Smooth Manifolds*, ch. 20 (FC08-C20-U003/U006): the

Published copy of a result from `LeanCategories.Topology.InvariantIntegralCurve`; the definition module keeps the original declaration, this file restates it, and the platform submission replaces the delegated proof with `by sorry`.
-/

@[expose] public section

namespace LeanCategories.Cards

open LeanCategories.Topology

open Bundle Function Manifold Set VectorField
open scoped ContDiff Manifold Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
open LeanCategories.Topology

/-- On a complete Lie group, the integral curve of an invariant vector field through a point
is defined for all times: it is an integral curve on the whole real line. -/
theorem LeanCategories_Topology_isMIntegralCurve_mulInvariantIntegralCurveData : ∀ [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (x : G),
    IsMIntegralCurve (mulInvariantIntegralCurveData v x) (mulInvariantVectorField v) :=
  LeanCategories.Topology.isMIntegralCurve_mulInvariantIntegralCurveData

end LeanCategories.Cards

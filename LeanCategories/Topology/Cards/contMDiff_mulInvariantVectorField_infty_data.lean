/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.InvariantIntegralCurve

/-! # Card: `LeanCategories.Topology.contMDiff_mulInvariantVectorField_infty_data`

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

/-- On a smooth Lie group, every invariant vector field is smooth. -/
theorem LeanCategories_Topology_contMDiff_mulInvariantVectorField_infty_data : ∀ [ContMDiffMul I ∞ G]
    (v : GroupLieAlgebra I G),
    ContMDiff I I.tangent ∞
      (fun g : G => (mulInvariantVectorField v g : TangentBundle I G)) :=
  LeanCategories.Topology.contMDiff_mulInvariantVectorField_infty_data

end LeanCategories.Cards

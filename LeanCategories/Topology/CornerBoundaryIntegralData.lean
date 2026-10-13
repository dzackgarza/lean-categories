/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic

/-!
# Boundary-integral data for manifolds with corners

Definition-level realization of Lee FC08-C16-U031.

For a boundary form supported in one oriented corner chart, Lee's definition is
the finite sum of the induced integrals over the coordinate faces of the model
orthant.  For an arbitrary compactly supported boundary form, Lee localizes by
a subordinate partition of unity and sums the chart-supported values.

The theorem layer is responsible for constructing such local presentations and
for proving that different charts/partitions give the same scalar.  Sweep III
must therefore not choose one arbitrary partition and call its value canonical.
Instead, this file records:

* the literal finite face-sum for one chart-supported form;
* the finite family of chart-supported pieces attached to any *supplied valid*
  partition presentation; and
* the exact graph characterizing the global integral by every such
  presentation.

The source integral is then represented by data carrying that exact graph. No
arbitrary functional is selected before chart compatibility, induced
orientation coherence, partition existence, or independence are proved.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open scoped BigOperators

universe u v w

/-- Lee's single-chart boundary integral on an oriented `n`-manifold with
corners.

`pullbackToFace i` is the pullback of the chart-supported boundary form to
the coordinate face `H_i`, and `integralFace i` is integration on that face
with the induced boundary orientation.  Those geometric operations are
supplied by their owners; this definition is exactly the displayed finite sum.
-/
def cornerBoundaryChartIntegral
    {n : ℕ}
    {ChartBoundaryForm : Type u}
    {FaceForm : Fin n → Type v}
    (pullbackToFace : ∀ i, ChartBoundaryForm → FaceForm i)
    (integralFace : ∀ i, FaceForm i → ℝ)
    (ω : ChartBoundaryForm) : ℝ :=
  ∑ i, integralFace i (pullbackToFace i ω)

/-- Data extracted from valid partition-of-unity presentations of compactly
supported boundary forms.

For a global form `ω`, `Presentation ω` is supplied by the ambient
manifold/partition owner and is intended to contain exactly the valid
subordinate chart presentations used by Lee.  `pieces ω P` lists the finitely
many nonzero chart-supported forms `ψ_i ω` occurring in the presentation.

Validity of a presentation, existence of presentations, and the theorem that
different presentations give the same integral are deliberately not proof
fields here.
-/
structure CornerBoundaryIntegralPresentationData
    (BoundaryForm : Type u) (ChartBoundaryForm : Type v) where
  Presentation : BoundaryForm → Type w
  pieces : ∀ ω, Presentation ω → List ChartBoundaryForm

/-- Scalar attached to one supplied valid partition presentation: sum the
single-chart boundary integrals of its localized pieces. -/
def cornerBoundaryPresentationIntegral
    {BoundaryForm : Type u} {ChartBoundaryForm : Type v}
    (D : CornerBoundaryIntegralPresentationData.{u, v, w}
      BoundaryForm ChartBoundaryForm)
    (localIntegral : ChartBoundaryForm → ℝ)
    (ω : BoundaryForm) (P : D.Presentation ω) : ℝ :=
  (D.pieces ω P).map localIntegral |>.sum

/-- Exact source graph for Lee's global corner-boundary integral.

A candidate functional has the source-defined value precisely when, for every
valid partition presentation, it equals the finite sum of the corresponding
single-chart values.  Consistency of this graph across different presentations
is the omitted well-definedness theorem.
-/
def IsCornerBoundaryIntegralData
    {BoundaryForm : Type u} {ChartBoundaryForm : Type v}
    (D : CornerBoundaryIntegralPresentationData.{u, v, w}
      BoundaryForm ChartBoundaryForm)
    (localIntegral : ChartBoundaryForm → ℝ)
    (integral : BoundaryForm → ℝ) : Prop :=
  ∀ (ω : BoundaryForm) (P : D.Presentation ω),
    integral ω = cornerBoundaryPresentationIntegral D localIntegral ω P

/-- Source-faithful global corner-boundary integral data: a functional
together with Lee's exact graph over every valid partition presentation. -/
abbrev CornerBoundaryIntegralData
    {BoundaryForm : Type u} {ChartBoundaryForm : Type v}
    (D : CornerBoundaryIntegralPresentationData.{u, v, w}
      BoundaryForm ChartBoundaryForm)
    (localIntegral : ChartBoundaryForm → ℝ) :=
  {integral : BoundaryForm → ℝ //
    IsCornerBoundaryIntegralData D localIntegral integral}

end LeanCategories.Topology

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Riemannian metric dual data

Definition-level realization of Lee FC08-C13-U039.

The pinned Riemannian-bundle API already stores the metric at a base point as a
continuous bilinear form.  Currying that form in its first argument is exactly
Lee's pointwise map `v ↦ g(v, -)` from a tangent fiber to its continuous dual.

Sweep III records only this fiberwise formula.  Fiberwise invertibility,
smoothness of the resulting bundle map, inverse-Gram-matrix formulas, and the
sharp/gradient constructions are separate result/dependent-definition content.
-/

@[expose] public section

namespace LeanCategories.Topology

open Bundle

universe uB uF

variable
  {EB : Type uB} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- The metric-dual covector of `v` at `b`, given by `w ↦ g_b(v,w)`.

For the tangent bundle this is Lee's bundle map `ĝ : TM → T*M` at the level of
its defining fiberwise formula. -/
def metricDualAt (g : ContMDiffRiemannianMetric IB n F E) (b : B) (v : E b) :
    E b →L[ℝ] ℝ :=
  g.inner b v

/-- Lee's flat/lowering-index notation at a fiber, naming the metric-dual map. -/
abbrev metricFlatAt (g : ContMDiffRiemannianMetric IB n F E) (b : B) (v : E b) :
    E b →L[ℝ] ℝ :=
  metricDualAt g b v

end LeanCategories.Topology

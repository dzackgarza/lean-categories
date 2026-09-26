/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

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

noncomputable section

namespace LeanCategories.Topology

open Bundle
open scoped ContDiff Manifold
open scoped BigOperators

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

/-- Coordinate lowering for a metric matrix: `X_j = Σ_i g_ij X^i`.

This is Lee FC08-C13-U040 at the data level. Identifying `g` and `X` with
the chart components of `metricDualAt` is a separate comparison statement. -/
def lowerIndexCoordinates {ι : Type*} [Fintype ι]
    (g : Matrix ι ι ℝ) (X : ι → ℝ) : ι → ℝ :=
  fun j => ∑ i, g i j * X i

/-- The raw total-space metric-dual map underlying Lee's
`hat(M) : TQ → T*Q` in FC08-C22-U033.

For the constant positive mass metric this sends `(q,v)` to the covector
`(q, M(v,-))`. Sweep III records only this dependent-pair map. Smoothness
and fibrewise invertibility are result-layer statements. -/
def metricDualBundleData (g : ContMDiffRiemannianMetric IB n F E) :
    (Σ b : B, E b) → (Σ b : B, E b →L[ℝ] ℝ) :=
  fun v => ⟨v.1, metricDualAt g v.1 v.2⟩

/-- Lee's mass-matrix coordinate form of the metric-dual construction
(FC08-C22-U033): `p_i = Σ_j M_ij v^j`.

No positivity, invertibility, or symmetry proof is needed to state the source
construction data. -/
def massMetricDualCoordinates {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (v : ι → ℝ) : ι → ℝ :=
  fun i => ∑ j, M i j * v j

/-- Source-faithful sharp/raising-index data at a fiber (FC08-C13-U043):
a vector together with Lee's exact defining equation `v♭ = ω`.

Existence and uniqueness are supplied later by the Riesz/isomorphism theorem;
no arbitrary vector is selected before those results. -/
abbrev MetricSharpAtData
    (g : ContMDiffRiemannianMetric IB n F E) (b : B)
    (alpha : E b →L[ℝ] ℝ) :=
  {v : E b // metricDualAt g b v = alpha}

/-- A source-facing family of valid sharp values on every fiber/covector.
Existence and smooth dependence remain theorem content. -/
abbrev MetricSharpSystemData
    (g : ContMDiffRiemannianMetric IB n F E) :=
  ∀ (b : B) (alpha : E b →L[ℝ] ℝ), MetricSharpAtData g b alpha

/-- Lee's inverse metric-coordinate matrix `(g^ij)` (FC08-C13-U042).

`Matrix.inv` is a total construction, so this declaration does not require a
proof that the supplied matrix is invertible. For a Riemannian Gram matrix,
nonsingularity and the inverse identities are separate result-layer facts. -/
noncomputable def inverseMetricCoordinates {ι : Type*} [Fintype ι]
    (g : Matrix ι ι ℝ) : Matrix ι ι ℝ := by
  classical
  exact g⁻¹

/-- Coordinate raising for a metric matrix: `ω^i = Σ_j g^ij ω_j`, using
Lee's inverse metric-coordinate matrix. Identifying this with supplied sharp
data for chart components is result/comparison content. -/
noncomputable def raiseIndexCoordinates {ι : Type*} [Fintype ι]
    (g : Matrix ι ι ℝ) (alpha : ι → ℝ) : ι → ℝ :=
  fun i => ∑ j, inverseMetricCoordinates g i j * alpha j

/-- Lee's gradient at a point (FC08-C13-U044): the sharp of the differential.

`mvfderiv` is Mathlib's manifold differential with normed-space target, so for
a smooth `f : B → ℝ` it is already a covector on `T_b B`. Smoothness of the resulting
section and the identity `g(grad f, v) = df(v)` are result content. -/
noncomputable def riemannianGradientAtData [IsManifold IB ∞ B]
    (g : ContMDiffRiemannianMetric IB ∞ EB
      (fun b : B => TangentSpace IB b))
    (D : MetricSharpSystemData g)
    (f : C^∞⟮IB, B; ℝ⟯) (b : B) : TangentSpace IB b :=
  (D b (mvfderiv IB f b)).1

/-- The pointwise vector field underlying Lee's gradient construction.
Smoothness is not bundled into this Sweep-III datum. -/
noncomputable def riemannianGradientData [IsManifold IB ∞ B]
    (g : ContMDiffRiemannianMetric IB ∞ EB
      (fun b : B => TangentSpace IB b))
    (D : MetricSharpSystemData g)
    (f : C^∞⟮IB, B; ℝ⟯) : ∀ b : B, TangentSpace IB b :=
  riemannianGradientAtData g D f

end LeanCategories.Topology

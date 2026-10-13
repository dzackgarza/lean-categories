/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Pseudo-Riemannian and Lorentz metric data

Definition-level realization of Lee FC08-C13-U047.

A pseudo-Riemannian metric is recorded exactly as a smooth family of symmetric,
nondegenerate continuous bilinear forms on tangent spaces together with one
signature shared by every point. The Lorentz condition is the source signature
condition `(d - 1, 1)` or `(1, d - 1)`.

No flat/sharp equivalence, signature invariance theorem, or smoothness consequence
is proved here. Those are result-layer obligations.
-/

@[expose] public noncomputable section

open ContinuousLinearMap
open scoped Manifold ContDiff

namespace LeanCategories.Topology

universe uE uH uM

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] [ChartedSpace H E]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

/-- Lee's smooth pseudo-Riemannian metric data.

The field `signature` is global data, and `signature_eq` states directly that
every tangent-space quadratic form has that same positive/negative signature. -/
structure PseudoRiemannianMetricData
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] where
  /-- The metric tensor at each point. -/
  val : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  /-- Symmetry of the metric tensor. -/
  symm : ∀ (x : M) (v w : TangentSpace I x), val x v w = val x w v
  /-- Pointwise nondegeneracy. -/
  nondegenerate : ∀ x : M, (val x).toBilinForm.Nondegenerate
  /-- Smooth dependence of the metric coefficients in extended-chart coordinates. -/
  smooth_in_charts : ∀ (x₀ : M) (v w : E),
    let e := extChartAt I x₀
    ContDiffWithinAt ℝ ∞
      (fun y => val (e.symm y)
        (mfderiv I I e.symm y v)
        (mfderiv I I e.symm y w))
      e.target (e x₀)
  /-- Common signature `(number of positive directions, number of negative directions)`. -/
  signature : ℕ × ℕ
  /-- Every point has the declared common signature. -/
  signature_eq : ∀ x : M,
    ((sigPos
        ((val x).toBilinForm.toQuadraticMap : QuadraticForm ℝ (TangentSpace I x)),
      sigNeg
        ((val x).toBilinForm.toQuadraticMap : QuadraticForm ℝ (TangentSpace I x)))) = signature

namespace PseudoRiemannianMetricData

variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

/-- The quadratic form associated to the metric at `x`, used only as existing
Mathlib data for reading its signature. -/
abbrev quadraticForm (g : PseudoRiemannianMetricData (M := M) I) (x : M) :
    QuadraticForm ℝ (TangentSpace I x) :=
  (g.val x).toBilinForm.toQuadraticMap

/-- Lee's Lorentz-metric condition: exactly one negative direction, or exactly
one positive direction under the opposite signature convention. -/
def IsLorentz (g : PseudoRiemannianMetricData (M := M) I) : Prop :=
  g.signature = (Module.finrank ℝ E - 1, 1) ∨
    g.signature = (1, Module.finrank ℝ E - 1)

end PseudoRiemannianMetricData

end LeanCategories.Topology

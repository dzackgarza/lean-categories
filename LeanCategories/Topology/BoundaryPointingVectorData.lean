/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Inward- and outward-pointing tangent-vector data

Definition-level realization of Lee FC08-C05-U055.

Lee defines inward- and outward-pointing vectors at a boundary point by
one-sided smooth curves, after excluding the tangent space of the boundary.
Pinned Mathlib owns the ambient manifold boundary and tangent fibres but does
not bundle the boundary itself as the smooth submanifold constructed in Lee
Theorem 5.11.  The missing boundary-tangent subset is therefore supplied by a
one-field interface.  Sweep III constructs only the source predicates below;
identifying this supplied subset with the tangent space of the canonical
boundary manifold is result-layer work.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open Set
open scoped Manifold

universe u v w

/-- Missing geometric interface for Lee FC08-C05-U055: which ambient tangent
vectors at a manifold-boundary point are tangent to the boundary submanifold.

No instance is manufactured here.  Lee Theorem 5.11 / FC08-C05-U016 is the
separate result that supplies the canonical boundary manifold whose tangent
image has this meaning. -/
structure BoundaryTangentInterface
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type w) [TopologicalSpace M] [ChartedSpace H M] where
  tangentAt : ∀ p : ↥(I.boundary M), Submodule ℝ (TangentSpace I p.1)

/-- A tangent vector at a boundary point is inward-pointing when it is not
boundary-tangent and is the positive one-sided velocity of a smooth curve.

The curve is represented by an arbitrary total map on the real line whose
restriction to [0, ε) is smooth; only that restriction and its within-derivative
are used, exactly matching the source half-interval datum. -/
def IsInwardPointing
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    (B : BoundaryTangentInterface I M)
    (p : ↥(I.boundary M)) (v : TangentSpace I p.1) : Prop :=
  v ∉ B.tangentAt p ∧
    ∃ ε : ℝ, 0 < ε ∧
      ∃ γ : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I ⊤ γ (Ico 0 ε) ∧
          γ 0 = p.1 ∧
          mfderivWithin 𝓘(ℝ, ℝ) I γ (Ico 0 ε) 0
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1) = v

/-- A tangent vector at a boundary point is outward-pointing when it is not
boundary-tangent and is the negative one-sided velocity of a smooth curve. -/
def IsOutwardPointing
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    (B : BoundaryTangentInterface I M)
    (p : ↥(I.boundary M)) (v : TangentSpace I p.1) : Prop :=
  v ∉ B.tangentAt p ∧
    ∃ ε : ℝ, 0 < ε ∧
      ∃ γ : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I ⊤ γ (Ioc (-ε) 0) ∧
          γ 0 = p.1 ∧
          mfderivWithin 𝓘(ℝ, ℝ) I γ (Ioc (-ε) 0) 0
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1) = v

end LeanCategories.Topology

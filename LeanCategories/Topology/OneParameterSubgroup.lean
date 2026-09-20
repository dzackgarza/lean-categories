/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# One-parameter subgroups of Lie groups

Definition-level realization of Lee FC08-C20-U001.  A one-parameter subgroup is
a smooth homomorphism from the additive real Lie group into `G`.  Generation by
a Lie-algebra element, automatic smoothness from continuity, and classification
are result content and are not included here.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace LeanCategories.Topology

universe u v

variable
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {G : Type v} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- Lee's defining predicate for a one-parameter subgroup of the Lie group `G`. -/
def IsOneParameterSubgroup (I : ModelWithCorners ℝ E H) [LieGroup I ∞ G]
    (γ : ℝ → G) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧
    γ 0 = 1 ∧
    ∀ s t : ℝ, γ (s + t) = γ s * γ t

end LeanCategories.Topology

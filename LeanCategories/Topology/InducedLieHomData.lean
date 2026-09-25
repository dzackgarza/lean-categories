/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-!
# Induced Lie-algebra homomorphism data

Definition-level realization of Lee FC08-C08-U061.

For a smooth Lie-group homomorphism `F : G → H`, the underlying linear map
of Lee's induced Lie-algebra homomorphism is the differential `dF₁` at the
identity. The preceding Theorem 8.44 is the result that this linear map
preserves Lie brackets and is characterized by `F`-related invariant vector
fields.

Sweep III therefore records `dF₁` directly and names the corresponding
`LieHom` by classical selection from the intrinsic predicate saying that its
underlying linear map is `dF₁`. No bracket-preservation proof is supplied as
constructor data.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Topology

open scoped ContDiff Manifold

universe u v w u' v' w'

variable
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H]
  {G : Type w} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {I : ModelWithCorners ℝ E H}
  {E' : Type u'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type v'} [TopologicalSpace H']
  {G' : Type w'} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  {I' : ModelWithCorners ℝ E' H'}

variable [LieGroup I (minSmoothness ℝ 3) G]
  [LieGroup I' (minSmoothness ℝ 3) G']

/-- The linear differential `dF₁` underlying Lee's induced Lie-algebra
homomorphism. The codomain rewrite uses only the monoid-homomorphism datum
`F(1)=1`. -/
def inducedLieLinearMapData
    (F : ContMDiffMonoidMorphism I I' ∞ G G') :
    GroupLieAlgebra I G →ₗ[ℝ] GroupLieAlgebra I' G' := by
  rw [← map_one F]
  exact (mfderiv I I' F (1 : G)).toLinearMap

/-- Intrinsic characterization of the induced Lie-algebra homomorphism:
its underlying linear map is the differential at the identity. -/
def IsInducedLieHomData
    (F : ContMDiffMonoidMorphism I I' ∞ G G')
    (φ : GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra I' G') : Prop :=
  φ.toLinearMap = inducedLieLinearMapData F

/-- Lee's induced Lie-algebra homomorphism, selected from the
`dF₁` characterization. Theorem 8.44 supplies the later proof that such a
Lie homomorphism exists and that the selected map has the intended
`F`-related-vector-field characterization. -/
def inducedLieHomData
    (F : ContMDiffMonoidMorphism I I' ∞ G G') :
    GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra I' G' :=
  Classical.epsilon (IsInducedLieHomData F)

end LeanCategories.Topology

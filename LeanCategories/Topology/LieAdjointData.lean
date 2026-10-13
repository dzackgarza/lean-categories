/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-!
# Adjoint differential data for Lie groups

Definition-level realization of Lee FC08-C20-U030.  Conjugation by a group
element is recorded as the raw map `h ↦ g * h * g⁻¹`, and `Ad(g)` is its
manifold differential at the identity.  Smoothness, invertibility, the
representation law, bracket preservation, and the identification
`d(Ad) = ad` are result content and are not included here.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff

namespace LeanCategories.Topology

universe u v

variable
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {G : Type v} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- Conjugation by `g`, as the raw map used in Lee's definition of `Ad(g)`. -/
def lieConjugation (g : G) : G → G :=
  fun h => g * h * g⁻¹

/-- Lee's group adjoint datum: the differential at the identity of conjugation
by `g`.  No automorphism or Lie-homomorphism laws are bundled into the
definition. -/
def adjointDifferential (I : ModelWithCorners ℝ E H) [LieGroup I ∞ G] (g : G) :
    GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G :=
  mfderiv I I (lieConjugation g) 1

end LeanCategories.Topology

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.RiemannSurfaceHomologyPeriodData
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Candidate integral homology-period image

Definition-level assembly toward Peters--Sterk FC11-C16-U026 from the native
holomorphic-form dual and the scalar integrals adapted from
mrdouglasny/jacobian-challenge at
8ce1ec28aed1c78b3b39d0bae26e2858c82f5143 (Apache-2.0).

The source denominator is the image of the homology-to-dual period map.
Constructing that map as a linear/additive map, and hence proving that its
image is a subgroup, is result work. Sweep III therefore records the exact
candidate carrier and the predicate saying that a supplied subgroup has that
carrier, but does not select a subgroup or form the quotient prematurely.

The Jacobian quotient itself remains blocked until the period-functional
linearity/additivity results are available.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff

namespace LeanCategories.Algebra

universe u

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- Exact carrier condition for the source period subgroup. Stating this
condition does not prove that the candidate set is closed under addition. -/
def IsCurveIntegralPeriodSubgroupData (x₀ : X)
    (P : AddSubgroup (CurveJacobianDualData X)) : Prop :=
  (P : Set (CurveJacobianDualData X)) =
    curveIntegralPeriodCandidateSetData (X := X) (x₀ := x₀)

end LeanCategories.Algebra

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.RiemannSurfaceHomologyPeriodData
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Raw Jacobian quotient by the integral period relation

Definition-level assembly toward Peters--Sterk FC11-C16-U026 from the native
holomorphic-form dual and the scalar integrals adapted from
mrdouglasny/jacobian-challenge at
8ce1ec28aed1c78b3b39d0bae26e2858c82f5143 (Apache-2.0).

The source denominator is the image of the homology-to-dual period map.
Constructing that map as a linear/additive map, and hence proving that its
image is a subgroup, is result work.

Sweep III avoids that proof obligation by recording the source equivalence
relation directly on the numerator: two dual functionals are related when
their difference is in the exact candidate period set. Lean's raw quotient
requires no proof that this relation is reflexive, symmetric, or transitive.
Once the result layer proves that the candidate set is the additive image of
integral homology, this raw quotient is exactly the source quotient
H⁰(C, Ω¹_C)ᵛ / ι(H₁(C, ℤ)).
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

/-- Raw period relation on the Hodge-theoretic numerator of the Jacobian.

This is the quotient relation from the source formula, stated without first
promoting the candidate period image to an additive subgroup. -/
def CurveIntegralPeriodRelationData (x₀ : X)
    (φ ψ : CurveJacobianDualData X) : Prop :=
  φ - ψ ∈ curveIntegralPeriodCandidateSetData (X := X) (x₀ := x₀)

/-- Peters--Sterk's Hodge-theoretic Jacobian carrier as a raw quotient by the
integral-period relation.

No quotient-group structure is asserted here. Reflexivity/symmetry/transitivity
of the relation and its compatibility with addition are precisely the
period-linearity/additivity results deferred to Sweep IV. -/
abbrev CurveJacobianQuotientData (x₀ : X) :=
  Quot (CurveIntegralPeriodRelationData X x₀)

/-- The canonical class of a dual functional in the raw Jacobian quotient. -/
def curveJacobianClassData (x₀ : X) (φ : CurveJacobianDualData X) :
    CurveJacobianQuotientData X x₀ :=
  Quot.mk _ φ

end LeanCategories.Algebra

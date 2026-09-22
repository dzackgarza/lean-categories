/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.RiemannSurfaceHomologyPeriodData
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The quotient by the integral homology-period image

Definition-level assembly toward Peters--Sterk FC11-C16-U026 from the native
holomorphic-form dual and the scalar integrals adapted from
mrdouglasny/jacobian-challenge at
8ce1ec28aed1c78b3b39d0bae26e2858c82f5143 (Apache-2.0).

The source denominator is the image of the homology-to-dual period map. That
raw map is defined at the homology-period owner by its full representative
equation. The subgroup is selected by its exact image carrier, following the
same definition-only boundary as the principal-divisor subgroup in this corpus.
This replaces the earlier generated-loop quotient model by the actual source
image presentation; there is no complex-linear span or topological closure.

The quotient and its projection use native additive-group owners. No period
map, subgroup, lattice, or Jacobian is supplied as an extra input. Selection
specifications, homomorphism laws, subgroup closure, basepoint independence,
and complex-torus properties remain result content and are not proved here.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff

namespace LeanCategories.Algebra

universe u

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The source set `ι(H₁(C, ℤ))`, using the raw homology-period map rather
than introducing a separate lattice or a chosen basis. -/
def curveIntegralPeriodImageData (x₀ : X) : Set (CurveJacobianDualData X) :=
  Set.range (curveHomologyPeriodFunctionalData (x₀ := x₀))

/-- Exact image-carrier condition for the period subgroup. Stating this
condition does not prove that the raw period map is additive. -/
def IsCurveIntegralPeriodSubgroupData (x₀ : X)
    (P : AddSubgroup (CurveJacobianDualData X)) : Prop :=
  (P : Set (CurveJacobianDualData X)) = curveIntegralPeriodImageData X x₀

/-- Period subgroup selected by the source image carrier. Existence and
the selection specification are separate result obligations. -/
def curveIntegralPeriodSubgroupData (x₀ : X) :
    AddSubgroup (CurveJacobianDualData X) :=
  Classical.epsilon (IsCurveIntegralPeriodSubgroupData X x₀)

/-- The source additive quotient `H⁰(C, Ω¹_C)ᵛ / ι(H₁(C, ℤ))`, with the
basepoint in the reference's homology presentation kept explicit. -/
abbrev CurveJacobianPeriodQuotientData (x₀ : X) :=
  CurveJacobianDualData X ⧸ curveIntegralPeriodSubgroupData X x₀

/-- Native additive quotient projection to the integral-period quotient. -/
def curveJacobianPeriodClassData (x₀ : X) :
    CurveJacobianDualData X →+ CurveJacobianPeriodQuotientData X x₀ :=
  QuotientAddGroup.mk' (curveIntegralPeriodSubgroupData X x₀)

/-- The reference's chosen-basepoint convention for the Jacobian carrier.
No independence of the basepoint, compactness, or manifold structure on
the quotient is asserted by this abbreviation. -/
abbrev CurveJacobianData [Nonempty X] :=
  CurveJacobianPeriodQuotientData X (Classical.arbitrary X)

end LeanCategories.Algebra

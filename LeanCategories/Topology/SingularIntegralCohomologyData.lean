/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.SingularCupProduct
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Raw integral singular cohomology data

Definition-level realization supporting Peters--Sterk FC11-C20-U046.

The source convention uses ordinary integral cohomology.  Sweep III records
the usual cochain-level data directly: the alternating-face coboundary,
degree-two cocycles, and the relation saying that two cocycles differ by a
coboundary.  The degree-two carrier is a raw `Quot` by that relation.

No proof that the coboundary squares to zero is required to form these data.
Consequently no subgroup/image inclusion, quotient-group structure, functorial
cohomology theory, or cup-product descent is asserted here.  Once the standard
`δ² = 0` result is available in Sweep IV, this raw quotient is exactly
`H²(X; ℤ)`.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace LeanCategories.Topology

universe u

variable (X : Type u) [TopologicalSpace X]

/-- The coface inclusion omitting vertex `i` in the standard topological
simplex. -/
def singularIntegralCofaceData {n : ℕ} (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map (fun j => i.succAbove j), stdSimplex.continuous_map _⟩

/-- The standard integral singular coboundary on raw cochains, written as the
alternating sum over cofaces. -/
def singularIntegralCoboundaryData (n : ℕ)
    (φ : RawSingularCochain X ℤ n) :
    RawSingularCochain X ℤ (n + 1) :=
  fun σ =>
    ∑ i : Fin (n + 2),
      (-1 : ℤ) ^ (i : ℕ) *
        φ (σ.comp (singularIntegralCofaceData i))

/-- Degree-two integral singular cocycles, defined only by the source equation
`δφ = 0`. -/
abbrev IntegralSingularTwoCocycleData :=
  {φ : RawSingularCochain X ℤ 2 //
    singularIntegralCoboundaryData X 2 φ = 0}

/-- Raw cohomology relation on degree-two cocycles: their difference is the
coboundary of an integral singular one-cochain. -/
def IntegralSingularTwoCohomologousData
    (φ ψ : IntegralSingularTwoCocycleData X) : Prop :=
  ∃ β : RawSingularCochain X ℤ 1,
    φ.1 - ψ.1 = singularIntegralCoboundaryData X 1 β

/-- Integral second singular cohomology as the raw quotient of degree-two
cocycles by the coboundary relation.

The later proof that `δ²=0` identifies this raw quotient with the ordinary
kernel/image quotient and supplies its additive-group structure. -/
abbrev IntegralSingularSecondCohomologyData :=
  Quot (IntegralSingularTwoCohomologousData X)

/-- Canonical raw cohomology class of a degree-two cocycle. -/
def integralSingularSecondCohomologyClassData
    (φ : IntegralSingularTwoCocycleData X) :
    IntegralSingularSecondCohomologyData X :=
  Quot.mk _ φ

end LeanCategories.Topology

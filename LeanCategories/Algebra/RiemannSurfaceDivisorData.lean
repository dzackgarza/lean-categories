/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Divisor data on compact Riemann surfaces

Definition-level port/adaptation for Peters--Sterk FC11-C16-U024 from
mrdouglasny/jacobian-challenge at revision
8ce1ec28aed1c78b3b39d0bae26e2858c82f5143.

The reference represents a divisor as the free abelian group on the points
of a compact Riemann surface and defines its degree by summing
coefficients. Its global meromorphic-function layer proves finite support
of the order function and proves that principal divisors form a subgroup.

Sweep III records only the source data. A nonzero rational function is
represented by the same chartwise meromorphic/nonzero-germ data used by
the reference. Its principal divisor is selected from the intrinsic
coefficient formula

  coeff_p(div(f)) = ord_p(f).

Finite support, the specification theorem for that selection, additivity of
f ↦ div(f), degree zero of principal divisors, and the equivalence-relation
laws are result content and are not proved here.
-/

@[expose] public noncomputable section

open scoped Manifold Topology

namespace LeanCategories.Algebra

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Meromorphy of a complex-valued function on a Riemann surface at a
point, computed in the canonical extended chart.

This is the definition-level part of the pinned reference's
MeromorphicAtX. -/
def curveMeromorphicAtData (f : X → ℂ) (p : X) : Prop :=
  MeromorphicAt
    (f ∘ (extChartAt 𝓘(ℂ) p).symm)
    (extChartAt 𝓘(ℂ) p p)

/-- Order of a meromorphic germ in the canonical extended chart.

Chart-independence is a theorem in the reference and is deliberately not
part of this declaration. -/
def curveOrderAtData (p : X) (f : X → ℂ) : WithTop ℤ :=
  meromorphicOrderAt
    (f ∘ (extChartAt 𝓘(ℂ) p).symm)
    (extChartAt 𝓘(ℂ) p p)

/-- Representative data for a nonzero rational/meromorphic function on a
compact Riemann surface.

The finite-order condition excludes the zero germ at every point. Quotienting
representatives by punctured-chart equality is useful for the reference's
function-field group, but is not needed to state the divisor definitions in
FC11-C16-U024. -/
structure NonzeroCurveRationalFunctionData
    (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] where
  toFun : X → ℂ
  meromorphicAt : ∀ p : X, curveMeromorphicAtData toFun p
  order_ne_top : ∀ p : X, curveOrderAtData p toFun ≠ ⊤

namespace NonzeroCurveRationalFunctionData

instance : CoeFun (NonzeroCurveRationalFunctionData X) (fun _ => X → ℂ) :=
  ⟨toFun⟩

end NonzeroCurveRationalFunctionData

/-- Divisors on a smooth complex curve: finite integral formal sums of
points. This is the exact carrier used by the pinned reference. -/
abbrev CurveDivisorData (X : Type u) := FreeAbelianGroup X

/-- The finite support of a divisor. -/
def curveDivisorSupportData (D : CurveDivisorData X) : Finset X :=
  (FreeAbelianGroup.toFinsupp D).support

/-- Degree of a divisor, the sum of all integer coefficients. -/
def curveDivisorDegreeData (X : Type u) : CurveDivisorData X →+ ℤ :=
  FreeAbelianGroup.lift (fun _ : X => (1 : ℤ))

/-- Intrinsic coefficient characterization of the principal divisor
div(f) = Σ_p ord_p(f) p. -/
def IsCurvePrincipalDivisorData
    (f : NonzeroCurveRationalFunctionData X)
    (D : CurveDivisorData X) : Prop :=
  ∀ p : X,
    FreeAbelianGroup.coeff p D =
      (curveOrderAtData p f.toFun).untop₀

/-- Principal divisor selected by the source coefficient formula.

The reference proves the order function has finite support. Sweep III
does not re-prove that result merely to manufacture a finite formal sum. -/
def curvePrincipalDivisorData
    (f : NonzeroCurveRationalFunctionData X) : CurveDivisorData X :=
  Classical.epsilon (IsCurvePrincipalDivisorData f)

namespace CurveDivisorData

/-- A divisor is principal when it is the selected divisor of some nonzero
rational function. -/
def IsPrincipalData (D : CurveDivisorData X) : Prop :=
  ∃ f : NonzeroCurveRationalFunctionData X,
    D = curvePrincipalDivisorData f

/-- Peters--Sterk linear equivalence:
D₁ ~ D₂ iff D₁ - D₂ = div(f) for some nonzero rational function f. -/
def LinearlyEquivalentData (D₁ D₂ : CurveDivisorData X) : Prop :=
  ∃ f : NonzeroCurveRationalFunctionData X,
    D₁ - D₂ = curvePrincipalDivisorData f

end CurveDivisorData

/-- Predicate characterizing the subgroup of principal divisors. -/
def IsCurvePrincipalDivisorSubgroupData
    (P : AddSubgroup (CurveDivisorData X)) : Prop :=
  ∀ D : CurveDivisorData X, D ∈ P ↔ D.IsPrincipalData

/-- Principal-divisor subgroup selected by its source carrier.

Closure under addition and negation follows from the result-level
principal-divisor homomorphism and is intentionally not reproved here. -/
def curvePrincipalDivisorSubgroupData :
    AddSubgroup (CurveDivisorData X) :=
  Classical.epsilon (IsCurvePrincipalDivisorSubgroupData (X := X))

/-- Picard group at the source's divisor-class level. -/
abbrev CurvePicardGroupData (X : Type u) [TopologicalSpace X]
    [ChartedSpace ℂ X] : Type u :=
  CurveDivisorData X ⧸ curvePrincipalDivisorSubgroupData (X := X)

end LeanCategories.Algebra

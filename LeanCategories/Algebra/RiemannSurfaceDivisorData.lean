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
the reference. Principal-divisor and linear-equivalence predicates are
stated directly through the intrinsic coefficient formula

  coeff_p(div(f)) = ord_p(f).

Finite support of the order function, existence/uniqueness of an actual
finite divisor with those coefficients, additivity of f ↦ div(f), degree
zero of principal divisors, subgroup closure, and the equivalence-relation
laws are result content and are not used to manufacture values here.
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

namespace CurveDivisorData

/-- A divisor is principal when its coefficients are the orders of some
nonzero rational function. This avoids selecting a finite divisor before
the finite-support result is available. -/
def IsPrincipalData (D : CurveDivisorData X) : Prop :=
  ∃ f : NonzeroCurveRationalFunctionData X,
    IsCurvePrincipalDivisorData f D

/-- Peters--Sterk linear equivalence:
D₁ ~ D₂ iff D₁ - D₂ = div(f) for some nonzero rational function f. -/
def LinearlyEquivalentData (D₁ D₂ : CurveDivisorData X) : Prop :=
  (D₁ - D₂).IsPrincipalData

end CurveDivisorData

/-- Predicate characterizing the subgroup of principal divisors. -/
def IsCurvePrincipalDivisorSubgroupData
    (P : AddSubgroup (CurveDivisorData X)) : Prop :=
  ∀ D : CurveDivisorData X, D ∈ P ↔ D.IsPrincipalData

end LeanCategories.Algebra

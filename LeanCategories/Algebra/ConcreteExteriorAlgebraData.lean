/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.GradedMonoid
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Concrete exterior-algebra data on alternating covectors

Definition-level realization of Lee FC08-C14-U018.

Lee's concrete exterior algebra is the direct sum of scalar-valued alternating
covectors, with multiplication given by the determinant-normalized wedge from
FC08-C14-U014. The source subsequently invokes Proposition 14.11 for the
associative and graded-anticommutative laws.

Sweep III records the carrier, homogeneous multiplication, total finite-sum
multiplication, and degree-zero unit as raw data. No semiring/algebra instance
is manufactured here: associativity, unit laws, and graded commutativity are
exactly the result-layer obligations catalogued in FC08-C14-U016.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u

/-- Lee's degree-k scalar covectors on V: alternating k-linear forms on the
algebraic dual V*. -/
abbrev ConcreteExteriorDegree
    (V : Type u) [AddCommGroup V] [Module ℝ V] (k : ℕ) :=
  AlternatingMap ℝ (Module.Dual ℝ V) ℝ (Fin k)

/-- Lee's underlying graded carrier Λ(V*), retaining only the nonnegative
degrees; the negative integer grades in the source are zero. -/
abbrev ConcreteExteriorCarrier
    (V : Type u) [AddCommGroup V] [Module ℝ V] :=
  DirectSum ℕ (ConcreteExteriorDegree V)

/-- The determinant-normalized wedge on homogeneous covectors.

AlternatingMap.domCoprod is the signed shuffle product. Multiplication
ℝ ⊗[ℝ] ℝ → ℝ and the canonical equivalence Fin k ⊕ Fin l ≃ Fin (k+l)
put it in Lee's degree convention. -/
def concreteExteriorWedge
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    {k l : ℕ}
    (ω : ConcreteExteriorDegree V k)
    (η : ConcreteExteriorDegree V l) :
    ConcreteExteriorDegree V (k + l) :=
  AlternatingMap.domDomCongr finSumFinEquiv
    ((TensorProduct.lid ℝ ℝ).toLinearMap.compAlternatingMap (ω.domCoprod η))

/-- The raw homogeneous multiplication datum of the concrete exterior algebra.

GradedMonoid.GMul contains only the degree-respecting multiplication function;
it carries no associativity, distributivity, unit, or commutativity proofs. -/
@[instance_reducible]
def concreteExteriorGMul
    (V : Type u) [AddCommGroup V] [Module ℝ V] :
    GradedMonoid.GMul (ConcreteExteriorDegree V) where
  mul := concreteExteriorWedge

/-- The total wedge product on the direct-sum carrier, defined by finite
bilinear extension of the homogeneous wedge.

This is a plain function, not a bundled multiplication with law fields. -/
def concreteExteriorMul
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    (x y : ConcreteExteriorCarrier V) :
    ConcreteExteriorCarrier V := by
  classical
  exact x.sum fun k ω =>
    y.sum fun l η =>
      DirectSum.of (ConcreteExteriorDegree V) (k + l)
        (concreteExteriorWedge ω η)

/-- The raw degree-zero unit of Lee's concrete exterior-algebra data. -/
def concreteExteriorOne
    (V : Type u) [AddCommGroup V] [Module ℝ V] :
    ConcreteExteriorCarrier V :=
  DirectSum.of (ConcreteExteriorDegree V) 0
    (AlternatingMap.constOfIsEmpty ℝ (Module.Dual ℝ V) (Fin 0) 1)

end LeanCategories.Algebra

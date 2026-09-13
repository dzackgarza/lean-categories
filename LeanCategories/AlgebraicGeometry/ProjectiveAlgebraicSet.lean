/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.ProjectiveZeroLocus

/-!
# Classical projective algebraic sets

Hartshorne, *Algebraic Geometry* (1977), Chapter I, §2, pp. 8--13
(FC06-C01-U041).

A subset of `P^n_k` is projective algebraic when it is the common zero set
`Z(T)` of a family of homogeneous polynomials.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- Predicate expressing Hartshorne's definition of a projective algebraic
subset of `P^n_k`.

Source: Hartshorne, Chapter I, §2, p. 9 (FC06-C01-U041). -/
def IsProjectiveAlgebraicSet {n : ℕ}
    (Y : Set (ProjectivePointSpace k n)) : Prop :=
  ∃ T : Set (ProjectiveHomogeneousPolynomial k n),
    Y = projectiveZeroLocus k T

/-- A projective algebraic set together with a chosen homogeneous equation
presentation. -/
structure ProjectiveAlgebraicSet (n : ℕ) where
  carrier : Set (ProjectivePointSpace k n)
  equations : Set (ProjectiveHomogeneousPolynomial k n)
  carrier_eq : carrier = projectiveZeroLocus k equations

/-- The chosen projective algebraic set satisfies Hartshorne's predicate. -/
theorem ProjectiveAlgebraicSet.isProjectiveAlgebraicSet {n : ℕ}
    (Y : ProjectiveAlgebraicSet k n) : IsProjectiveAlgebraicSet k Y.carrier :=
  ⟨Y.equations, Y.carrier_eq⟩

end LeanCategories.AlgebraicGeometry

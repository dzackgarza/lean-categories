/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Nonnegatively graded ring data

Definition-level realization of Hatcher FC07-C03-U020, adapted from the
pinned ATLAS graded-algebra interface.

Hatcher defines a graded ring as a direct sum `A = ⨁ k ≥ 0, A_k` whose
multiplication sends `A_k × A_l` to `A_{k+l}`. In this context he uses
"commutative" for the Koszul sign rule

`a * b = (-1)^(|a||b|) b * a`.

`DirectSum.GRing` already packages the additive groups, degree-compatible
multiplication, unit, and ordinary ring laws at the graded-family level.
This file only defines the source structure and its graded-commutativity
predicate. It constructs no instance and proves no law.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

open DirectSum GradedMonoid

/-- Hatcher's nonnegatively graded ring data
`A = ⨁ k ≥ 0, A_k`.

The degree of a homogeneous product is encoded by the result type of
`GradedMonoid.GMul.mul`. -/
structure GradedRingData where
  A : ℕ → Type u
  instAddCommGroup : ∀ k, AddCommGroup (A k)
  instGRing : DirectSum.GRing A

attribute [instance] GradedRingData.instAddCommGroup GradedRingData.instGRing

namespace GradedRingData

/-- Multiplication of homogeneous elements in a graded ring. -/
def mul (G : GradedRingData) {p q : ℕ}
    (x : G.A p) (y : G.A q) : G.A (p + q) :=
  GradedMonoid.GMul.mul x y

/-- Hatcher's convention for a commutative graded ring: homogeneous elements
of degrees `p` and `q` commute with the Koszul sign `(-1)^(pq)`. -/
def IsGradedCommutative (G : GradedRingData) : Prop :=
  ∀ (p q : ℕ) (x : G.A p) (y : G.A q),
    GradedMonoid.GMul.mul x y =
      ((((p : ℤ) * (q : ℤ)).negOnePow : ℤ) •
        cast (congrArg G.A (Nat.add_comm q p))
          (GradedMonoid.GMul.mul y x))

end GradedRingData

end LeanCategories.Algebra

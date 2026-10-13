/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.RingTheory.Ideal.Over

/-!
# Double-coset prime data

Definition-level realization of Neukirch FC09-C01-U077.

Mathlib already provides the double-coset setoid and quotient
`DoubleCoset.Quotient H D`.  Neukirch's arithmetic construction is represented
before quotient descent by the formula

`σ ↦ (σ • P) ∩ L`.

In Lean, contraction to the lower ring is `Ideal.under`.  This file records
only that representative-level function.  Proving that it takes values in the
appropriate primes-over subtype, is constant on double cosets, descends to the
quotient, and induces a bijection are result-layer obligations.
-/

@[expose] public noncomputable section

open scoped Pointwise

namespace LeanCategories.Algebra

universe uA uC uG

variable
  {A : Type uA} [CommSemiring A]
  {C : Type uC} [Semiring C] [Algebra A C]
  {G : Type uG} [Group G] [MulSemiringAction G C]

/-- The representative-level arithmetic rule in Neukirch FC09-C01-U077:
`σ ↦ (σ • P) ∩ A`.

The source later regards this as a function on a double-coset quotient.  The
descent assertion is deliberately not part of this definition. -/
def doubleCosetPrimeRepresentativeData (P : Ideal C) (σ : G) : Ideal A :=
  (σ • P).under A

end LeanCategories.Algebra

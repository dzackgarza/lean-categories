/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Kostant PBW monomial data

Humphreys FC14-C07-U025. This file records the ordered divided-power,
Cartan-binomial and triangular PBW monomials. Their linear independence,
spanning, and integral-form basis theorems belong to later result units.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace LeanCategories.Algebra

universe u v w x

variable (K : Type u) (L : Type v)
variable [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]

/-- The divided power `x^n / n!` in `U(L)`. -/
def ueaDividedPower (x : L) (n : ℕ) : UniversalEnvelopingAlgebra K L :=
  ((Nat.factorial n : K)⁻¹) • (UniversalEnvelopingAlgebra.ι K x) ^ n

/-- The Cartan binomial `binom(h,n)` evaluated inside `U(L)`. -/
def ueaCartanBinomial (h : L) (n : ℕ) : UniversalEnvelopingAlgebra K L :=
  ((Nat.factorial n : K)⁻¹) •
    ((List.range n).map fun j : ℕ =>
      (UniversalEnvelopingAlgebra.ι K h -
        algebraMap K (UniversalEnvelopingAlgebra K L) (j : K))).prod

/-- Ordered product of divided powers for a supplied root order. -/
def orderedDividedPowerProduct {I : Type w}
    (order : List I) (x : I → L) (n : I → ℕ) :
    UniversalEnvelopingAlgebra K L :=
  (order.map fun i => ueaDividedPower K L (x i) (n i)).prod

/-- Ordered product of Cartan binomials for a supplied Cartan order. -/
def orderedCartanBinomialProduct {I : Type x}
    (order : List I) (h : I → L) (n : I → ℕ) :
    UniversalEnvelopingAlgebra K L :=
  (order.map fun i => ueaCartanBinomial K L (h i) (n i)).prod

/-- Humphreys' triangular Kostant PBW monomial `f_A h_B e_C`. -/
def kostantPBWElement {Phi : Type w} {I : Type x}
    (negativeOrder positiveOrder : List Phi) (cartanOrder : List I)
    (xNeg xPos : Phi → L) (h : I → L)
    (A C : Phi → ℕ) (B : I → ℕ) : UniversalEnvelopingAlgebra K L :=
  orderedDividedPowerProduct K L negativeOrder xNeg A *
    orderedCartanBinomialProduct K L cartanOrder h B *
    orderedDividedPowerProduct K L positiveOrder xPos C

end LeanCategories.Algebra

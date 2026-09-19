/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import Mathlib.Order.Lattice.Nat

/-!
# Weyl-group length and inversion data

Humphreys FC14-C03-U027. The two numerical constructions are recorded
separately; their equality is FC14-C03-U028 and is not part of Sweep III.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (P : RootPairing ι R M N)

/-- Lengths of simple-reflection words, relative to the chosen base, representing `w`. -/
def baseWeylWordLengths (b : P.Base) (w : P.weylGroup) : Set ℕ :=
  {n | ∃ omega : List b.support,
    omega.length = n ∧
      (omega.map fun i => P.weylGroup.ofIdx i.1).prod = w}

/-- Humphreys' length: the least length of a simple-reflection word representing `w`.

The `sInf` is total; existence of such a word is result/generation content rather than
a constructor field. -/
def baseWeylLength (b : P.Base) (w : P.weylGroup) : ℕ :=
  sInf (baseWeylWordLengths P b w)

/-- Positive roots sent to negative roots by `w`, represented on the finite root-index set. -/
def baseWeylInversions [Fintype ι] [CharZero R] (b : P.Base) (w : P.weylGroup) : Finset ι := by
  classical
  exact Finset.univ.filter fun i =>
    b.IsPos i ∧ ¬ b.IsPos (P.weylGroupToPerm w i)

/-- Humphreys' inversion number `n(w)`. -/
def baseWeylInversionNumber [Fintype ι] [CharZero R]
    (b : P.Base) (w : P.weylGroup) : ℕ :=
  (baseWeylInversions P b w).card

end LeanCategories.Algebra

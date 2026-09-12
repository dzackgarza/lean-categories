/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.MixedComplex

/-!
# Trivial mixed complexes

Weibel, *An Introduction to Homological Algebra* (1994), Trivial Mixed
Complexes 9.8.8, pp. 344--353 (FC05-C09-U123).

Any nonnegative chain complex `(C,b)` is a mixed complex with `B=0`.
The resulting direct-sum formula for cyclic homology is result-level content.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A chain complex regarded as a mixed complex with zero Connes operator. -/
def trivialMixedComplex (K : ChainComplex C ℕ) : MixedComplex C where
  chain := K
  B := fun _ => 0
  B_sq := by
    intro n
    simp
  mixed_zero := by simp
  mixed_succ := by
    intro n
    simp

end LeanCategories.Homological

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Mixed complexes

Weibel, *An Introduction to Homological Algebra* (1994), Definition 9.8.1,
pp. 344--353 (FC05-C09-U113).

A mixed complex is a nonnegative chain complex `(M,b)` together with a
degree-raising operator `B` satisfying `B²=0` and `bB+Bb=0`.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- Weibel's mixed complex `(M,b,B)`.  The chain-complex structure on `M`
already contains `b²=0`; the remaining fields are `B²=0` and the mixed
anticommutation identity. -/
structure MixedComplex where
  /-- The underlying nonnegative chain complex `(M,b)`. -/
  chain : ChainComplex C ℕ
  /-- Connes' degree-raising operator `B : M_n → M_{n+1}`. -/
  B : ∀ n : ℕ, chain.X n ⟶ chain.X (n + 1)
  /-- `B²=0`. -/
  B_sq : ∀ n : ℕ, B n ≫ B (n + 1) = 0
  /-- The degree-zero instance of `bB+Bb=0`; the missing downward term from
  degree zero is zero. -/
  mixed_zero : B 0 ≫ chain.d 1 0 = 0
  /-- `bB+Bb=0` in every positive degree. -/
  mixed_succ : ∀ n : ℕ,
    chain.d (n + 1) n ≫ B n + B (n + 1) ≫ chain.d (n + 2) (n + 1) = 0

end LeanCategories.Homological

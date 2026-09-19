/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.StdBasis

@[expose] public noncomputable section

open scoped BigOperators

namespace LeanCategories.Algebra

def standardCoordinate {n : ℕ} (i : Fin n) : Fin n → ℝ :=
  Pi.single i 1

def typeAAmbient (l : ℕ) : Set (Fin (l + 1) → ℝ) :=
  {x | ∑ i, x i = 0}

def typeARootSet (l : ℕ) : Set (Fin (l + 1) → ℝ) :=
  {x | ∃ i j : Fin (l + 1), i ≠ j ∧
    x = standardCoordinate i - standardCoordinate j}

def typeASimpleRoot (l : ℕ) (i : Fin l) : Fin (l + 1) → ℝ :=
  standardCoordinate i.castSucc - standardCoordinate i.succ

end LeanCategories.Algebra

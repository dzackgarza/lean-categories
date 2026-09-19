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

def coordinateSign : Bool → ℝ
  | true => 1
  | false => -1

def typeBRootSet (l : ℕ) : Set (Fin l → ℝ) :=
  {x |
    (∃ i : Fin l, ∃ s : Bool,
      x = coordinateSign s • standardCoordinate i) ∨
    (∃ i j : Fin l, i ≠ j ∧ ∃ s t : Bool,
      x = coordinateSign s • standardCoordinate i +
        coordinateSign t • standardCoordinate j)}

def typeBSimpleRoot (l : ℕ) (i : Fin l) : Fin l → ℝ := by
  classical
  if h : i.1 + 1 < l then
    exact standardCoordinate i - standardCoordinate ⟨i.1 + 1, h⟩
  else
    exact standardCoordinate i

def typeCRootSet (l : ℕ) : Set (Fin l → ℝ) :=
  {x |
    (∃ i : Fin l, ∃ s : Bool,
      x = (2 * coordinateSign s) • standardCoordinate i) ∨
    (∃ i j : Fin l, i ≠ j ∧ ∃ s t : Bool,
      x = coordinateSign s • standardCoordinate i +
        coordinateSign t • standardCoordinate j)}

def typeCSimpleRoot (l : ℕ) (i : Fin l) : Fin l → ℝ := by
  classical
  if h : i.1 + 1 < l then
    exact standardCoordinate i - standardCoordinate ⟨i.1 + 1, h⟩
  else
    exact (2 : ℝ) • standardCoordinate i

def typeDRootSet (l : ℕ) : Set (Fin l → ℝ) :=
  {x | ∃ i j : Fin l, i ≠ j ∧ ∃ s t : Bool,
    x = coordinateSign s • standardCoordinate i +
      coordinateSign t • standardCoordinate j}

def typeDSimpleRootSet : (l : ℕ) → Set (Fin l → ℝ)
  | 0 => ∅
  | 1 => ∅
  | n + 2 =>
      {x |
        (∃ i : Fin (n + 1),
          x = standardCoordinate i.castSucc - standardCoordinate i.succ) ∨
        x = standardCoordinate (Fin.last n).castSucc +
          standardCoordinate (Fin.last (n + 1))}

end LeanCategories.Algebra

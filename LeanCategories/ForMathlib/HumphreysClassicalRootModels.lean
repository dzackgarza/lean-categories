/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Humphreys' classical crystallographic root models

Humphreys, *Reflection Groups and Coxeter Groups*, Section 2.10, pp. 41--42
(FC15-C02-U027), constructs the classical root systems `Aₙ`, `Bₙ`, `Cₙ`, and `Dₙ` in standard
Euclidean coordinates and displays a simple system for each.

This file records exactly the coordinate carriers and displayed simple systems. The assertions that
these carriers satisfy the root-system axioms, the formulas for the highest roots, and the concrete
descriptions of the Weyl groups are results about these data and are not included here.
-/

namespace LeanCategories.HumphreysClassicalRoots

/-- Standard real coordinate space of dimension `n`. -/
abbrev Space (n : ℕ) := Fin n → ℝ

/-- The standard lattice `ℤⁿ ⊂ ℝⁿ`, written as a coordinate predicate. -/
def standardLattice (n : ℕ) : Set (Space n) :=
  {x | ∃ z : Fin n → ℤ, x = fun i ↦ (z i : ℝ)}

/-- Squared Euclidean length in standard coordinates. -/
def squaredLength {n : ℕ} (x : Space n) : ℝ :=
  ∑ i, x i * x i

/-- The standard coordinate vector `e_i`. -/
def coordinate {n : ℕ} (i : Fin n) : Space n :=
  Pi.single i 1

/-- A scalar is one of the two signs used in the displayed root formulas. -/
def IsSign (epsilon : ℝ) : Prop :=
  epsilon = 1 ∨ epsilon = -1

/-- The roots `± scale * e_i`. -/
def signedAxisRoots (scale : ℝ) (n : ℕ) : Set (Space n) :=
  {x | ∃ (i : Fin n) (epsilon : ℝ), IsSign epsilon ∧
    x = (epsilon * scale) • coordinate i}

/-- The roots `±e_i ± e_j` with `i ≠ j`. -/
def signedPairRoots (n : ℕ) : Set (Space n) :=
  {x | ∃ (i j : Fin n) (epsilon delta : ℝ), i ≠ j ∧ IsSign epsilon ∧ IsSign delta ∧
    x = epsilon • coordinate i + delta • coordinate j}

/-- The chain roots `e_i - e_{i+1}` in `ℝⁿ`. -/
def adjacentDifferenceRoots (n : ℕ) : Set (Space n) :=
  {x | ∃ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 ∧ x = coordinate i - coordinate j}

/-! ## Type A -/

/-- Humphreys' ambient hyperplane for `Aₙ`: the coordinates in `ℝⁿ⁺¹` sum to zero. -/
def typeAAmbient (n : ℕ) : Set (Space (n + 1)) :=
  {x | ∑ i, x i = 0}

/-- Humphreys' `Aₙ` root carrier: lattice vectors in the ambient hyperplane of squared length two. -/
def typeARootCarrier (n : ℕ) : Set (Space (n + 1)) :=
  {x | x ∈ typeAAmbient n ∧ x ∈ standardLattice (n + 1) ∧ squaredLength x = 2}

/-- Humphreys' displayed simple system `e₁-e₂, …, eₙ-eₙ₊₁` for `Aₙ`. -/
def typeASimpleRoots (n : ℕ) : Set (Space (n + 1)) :=
  adjacentDifferenceRoots (n + 1)

/-! ## Type B -/

/-- Humphreys' `Bₙ` root carrier: standard-lattice vectors of squared length one or two. -/
def typeBRootCarrier (n : ℕ) : Set (Space n) :=
  {x | x ∈ standardLattice n ∧ (squaredLength x = 1 ∨ squaredLength x = 2)}

/-- Humphreys' displayed simple system for `Bₙ`: the adjacent differences together with `eₙ`. -/
def typeBSimpleRoots (n : ℕ) : Set (Space n) :=
  adjacentDifferenceRoots n ∪
    {x | ∃ i : Fin n, (i : ℕ) + 1 = n ∧ x = coordinate i}

/-! ## Type C -/

/-- Humphreys' displayed `Cₙ` roots: `±2e_i` and `±e_i ± e_j`. -/
def typeCRootCarrier (n : ℕ) : Set (Space n) :=
  signedAxisRoots 2 n ∪ signedPairRoots n

/-- Humphreys' displayed simple system for `Cₙ`: the adjacent differences together with `2eₙ`. -/
def typeCSimpleRoots (n : ℕ) : Set (Space n) :=
  adjacentDifferenceRoots n ∪
    {x | ∃ i : Fin n, (i : ℕ) + 1 = n ∧ x = (2 : ℝ) • coordinate i}

/-! ## Type D -/

/-- Humphreys' `Dₙ` root carrier: standard-lattice vectors of squared length two. -/
def typeDRootCarrier (n : ℕ) : Set (Space n) :=
  {x | x ∈ standardLattice n ∧ squaredLength x = 2}

/-- Humphreys' displayed simple system for `Dₙ`: the adjacent differences together with
`e_{n-1} + e_n` (using one-based source indices). -/
def typeDSimpleRoots (n : ℕ) : Set (Space n) :=
  adjacentDifferenceRoots n ∪
    {x | ∃ i j : Fin n, (i : ℕ) + 2 = n ∧ (j : ℕ) + 1 = n ∧
      x = coordinate i + coordinate j}

end LeanCategories.HumphreysClassicalRoots

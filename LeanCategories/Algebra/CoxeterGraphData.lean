/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan

@[expose] public noncomputable section

open Classical

namespace LeanCategories.Algebra

/-- A **Coxeter diagram**: a vertex set carrying symmetric, nonnegative rational edge
weights.

This replaces the former bare alias `CoxeterGraphData ι := ι → ι → ℕ`. The diagram of a
finite root set records, on the edge between roots `r` and `s`, the normalized pairing
square `(r, s)² / (r² s²)` (`LeanCategories.Lattices.Valued.coxeterDiagramOfRoots`), a
rational number; the diagram read off a Cartan matrix records the edge multiplicity
`a_ij a_ji` (`coxeterGraphOfCartanMatrix`). The Coxeter order `m(r, s)` of an edge is
derived from its weight where it exists (theorem content): the weight is not the order, and
neither is a Gram entry — the Gram entry of a Coxeter diagram with label `m` is
`−2 cos (π / m)` with diagonal `2`. -/
structure CoxeterDiagram (ι : Type*) where
  /-- The edge weight between two vertices. -/
  edges : ι → ι → ℚ
  /-- Edge weights are nonnegative. -/
  edges_nonneg : ∀ i j, 0 ≤ edges i j
  /-- The weight is symmetric. -/
  edges_symm : ∀ i j, edges i j = edges j i

/-- Humphreys FC14-C03-U039: off-diagonal edge multiplicity `a_ij a_ji` from supplied
Cartan-matrix data, as the edge weights of a Coxeter diagram; the diagonal carries no edge.
Value bounds and conversion to Coxeter orders are theorem content. -/
noncomputable def coxeterGraphOfCartanMatrix {ι : Type*}
    (A : Matrix ι ι ℤ) : CoxeterDiagram ι where
  edges i j := if i = j then 0 else (Int.toNat (A i j * A j i) : ℚ)
  edges_nonneg i j := by
    by_cases h : i = j
    · simp [h]
    · simp only [h, if_false]
      exact Nat.cast_nonneg _
  edges_symm i j := by
    by_cases h : i = j
    · simp [h]
    · simp only [h, Ne.symm h, if_false, mul_comm]

end LeanCategories.Algebra

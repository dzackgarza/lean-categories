/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.GroupCyclicComponents
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Cyclic operator on the simplicial classifying space

Weibel, *An Introduction to Homological Algebra* (1994), Example 9.6.2,
pp. 330--337 (FC05-C09-U083).

In simplicial degree `n`, the classifying simplicial set has tuples
`(g₁,…,gₙ) ∈ G^n`.  Its cyclic operator is
`((g₁⋯gₙ)⁻¹,g₁,…,gₙ₋₁)`.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u

variable (G : Type u) [Group G]

/-- The degreewise cyclic operator on the tuple model of `BG`. -/
def classifyingSpaceCyclicData : ∀ n : ℕ, (Fin n → G) → (Fin n → G)
  | 0, _ => fun i => Fin.elim0 i
  | n + 1, a =>
      Fin.cons (finTupleProduct G (n + 1) a)⁻¹
        (fun j : Fin n => a j.castSucc)

end LeanCategories.Homological

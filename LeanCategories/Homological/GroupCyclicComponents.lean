/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Conjugacy-class components of group Hochschild chains

Weibel, *An Introduction to Homological Algebra* (1994), Definition 9.7.3,
pp. 338--343 (FC05-C09-U103).
-/

@[expose] public section

namespace LeanCategories.Homological

universe u

variable (G : Type u) [Group G]

/-- Ordered product of a finite tuple in a possibly noncommutative group. -/
def finTupleProduct : ∀ n : ℕ, (Fin n → G) → G
  | 0, _ => 1
  | n + 1, a => finTupleProduct n (fun i => a i.castSucc) * a (Fin.last n)

/-- The degree-`n` tuple component whose ordered product lies in the conjugacy class
of `x`.  This is Weibel's `Z_n(G,x)`. -/
def GroupCyclicComponent (x : G) (n : ℕ) : Set (Fin (n + 1) → G) :=
  {a | IsConj (finTupleProduct G (n + 1) a) x}

/-- Membership in `Z_n(G,x)` is exactly the conjugacy-class condition. -/
theorem mem_groupCyclicComponent (x : G) (n : ℕ) (a : Fin (n + 1) → G) :
    a ∈ GroupCyclicComponent G x n ↔ IsConj (finTupleProduct G (n + 1) a) x :=
  Iff.rfl

end LeanCategories.Homological

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Shuffle elements in symmetric-group rings

Weibel, *An Introduction to Homological Algebra* (1994), Definition in §9.4,
pp. 319--325 (FC05-C09-U066).

For `p+q=n`, `s_{pq} ∈ ℤΣ_n` is the signed sum of all `(p,q)`-shuffles,
and `s_n` is the sum of `s_{p,n-p}` over `0<p<n`.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open scoped BigOperators

/-- A permutation of `Fin n` is a shuffle at cutoff `p` when it preserves order
on the indices below `p` and separately on the indices at least `p`.
For `n=p+q` this is the usual `(p,q)`-shuffle condition. -/
def IsShuffleAt {n : ℕ} (p : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ i j : Fin n, i < j → (i : ℕ) < p → (j : ℕ) < p → σ i < σ j) ∧
  (∀ i j : Fin n, i < j → p ≤ (i : ℕ) → p ≤ (j : ℕ) → σ i < σ j)

/-- The signed shuffle sum in `ℤ[Σ_n]` at a fixed cutoff `p`. -/
noncomputable def shuffleElementAt (n p : ℕ) :
    MonoidAlgebra ℤ (Equiv.Perm (Fin n)) := by
  classical
  exact ∑ σ : Equiv.Perm (Fin n),
    if IsShuffleAt p σ then
      MonoidAlgebra.single σ ((Equiv.Perm.sign σ : ℤˣ) : ℤ)
    else 0

/-- Weibel's `(p,q)`-shuffle element `s_{pq} ∈ ℤΣ_{p+q}`. -/
noncomputable def shuffleElement (p q : ℕ) :
    MonoidAlgebra ℤ (Equiv.Perm (Fin (p + q))) :=
  shuffleElementAt (p + q) p

/-- Weibel's total shuffle element
`s_n = Σ_{0<p<n} s_{p,n-p} ∈ ℤΣ_n`. -/
noncomputable def totalShuffleElement (n : ℕ) :
    MonoidAlgebra ℤ (Equiv.Perm (Fin n)) := by
  classical
  exact ∑ p ∈ (Finset.range n).filter (0 < ·), shuffleElementAt n p

end LeanCategories.Homological

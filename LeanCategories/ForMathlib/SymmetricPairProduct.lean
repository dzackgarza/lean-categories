/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Products over increasing pairs

A product of a symmetric function over increasing index pairs does not change when the
indices are permuted.
-/

@[expose] public section

namespace LeanCategories.ForMathlib

/-- Permuting the indices leaves a product of a symmetric function over increasing pairs
unchanged. -/
theorem prod_increasing_pairs_comp_perm {α : Type*} {M : Type*} [CommMonoid M] {n : ℕ}
    (f : α → α → M) (hf : ∀ a b, f a b = f b a) (w : Fin n → α) (e : Equiv.Perm (Fin n)) :
    (∏ p : Fin n × Fin n with p.1 < p.2, f (w (e p.1)) (w (e p.2))) =
      ∏ p : Fin n × Fin n with p.1 < p.2, f (w p.1) (w p.2) := by
  refine Finset.prod_nbij'
    (fun p => if e p.1 < e p.2 then (e p.1, e p.2) else (e p.2, e p.1))
    (fun q => if e.symm q.1 < e.symm q.2 then (e.symm q.1, e.symm q.2)
      else (e.symm q.2, e.symm q.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have hne : e p.1 ≠ e p.2 := fun h => absurd (e.injective h) hp.ne
    split_ifs with h
    · exact h
    · exact lt_of_le_of_ne (not_lt.mp h) hne.symm
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    have hne : e.symm q.1 ≠ e.symm q.2 := fun h => absurd (e.symm.injective h) hq.ne
    split_ifs with h
    · exact h
    · exact lt_of_le_of_ne (not_lt.mp h) hne.symm
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases h : e p.1 < e p.2
    · rw [if_pos h]
      simp [Equiv.symm_apply_apply, hp]
    · rw [if_neg h]
      simp [Equiv.symm_apply_apply, asymm hp]
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    by_cases h : e.symm q.1 < e.symm q.2
    · rw [if_pos h]
      simp [Equiv.apply_symm_apply, hq]
    · rw [if_neg h]
      simp [Equiv.apply_symm_apply, asymm hq]
  · intro p hp
    split_ifs with h <;> simp [hf (w (e p.2)) (w (e p.1))]

end LeanCategories.ForMathlib

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
    (fun q => if e.symm q.1 < e.symm q.2 then (e.symm q.1, e.symm q.2) else
      (e.symm q.2, e.symm q.1)) ?_ ?_ ?_ ?_ ?_ <;>
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hne : ¬ (_ : Fin n) = _ := fun h => absurd (by simpa using congrArg _ h) hp.ne
    rcases lt_or_gt_of_ne hne with h | h <;>
      simp_all [Prod.ext_iff, hf, ne_of_gt, asymm]

end LeanCategories.ForMathlib

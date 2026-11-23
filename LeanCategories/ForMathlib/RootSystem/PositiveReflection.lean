/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import Mathlib.LinearAlgebra.RootSystem.RootPositive
public import Mathlib.Tactic

/-!
# Positivity under a simple reflection, for arbitrary root index

This is the finite-root-free form of `RootPairing.Base.IsPos.reflectionPerm`.  The proof uses
only root-base expansions and reducedness, so it applies to the full AET root orbit even when the
Weyl group or a standard parabolic is infinite.

Provenance: the argument is the arbitrary-index replacement for the corresponding step in
TauCeti's `LinearAlgebra/RootSystem/Inversions/StrongExchange.lean` (Tau Ceti contributors,
Apache 2.0).  LC-09 queries and the direct TauCeti source hit are recorded in
`.scratch/wt181/lc09-foundation-2.txt` and `.scratch/wt181/lc09-gallery-3.txt`.
-/

@[expose] public section

noncomputable section

namespace RootPairing.Base

open Set Function

variable {ι M N : Type*} [AddCommGroup M] [Module ℝ M]
  [AddCommGroup N] [Module ℝ N]
  (P : RootPairing ι ℝ M N) [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-- A simple reflection preserves every positive root other than its own simple root.  Unlike
`RootPairing.Base.IsPos.reflectionPerm` in the current finite-root API, this proof uses only the
base expansion and reducedness, and therefore works for the full AET root orbit. -/
lemma isPos_reflectionPerm_of_ne {i j : ι} (hi : i ∈ b.support)
    (hj : b.IsPos j) (hji : j ≠ i) : b.IsPos (P.reflectionPerm i j) := by
  classical
  obtain ⟨f, hfSupport, hfSign, hf⟩ := b.exists_root_eq_sum_int j
  have hfpos : 0 < f := by
    rcases hfSign with hpos | hneg
    · exact hpos
    · exfalso
      have hnegSum : ∑ k ∈ b.support, f k < 0 := by
        apply Finset.sum_neg' (fun k _ ↦ hneg.le k)
        obtain ⟨k, hk⟩ := (Pi.lt_def.mp hneg).2
        exact ⟨k, hfSupport (ne_of_lt hk), hk⟩
      have hposSum : 0 < ∑ k ∈ b.support, f k := by
        rw [← b.height_eq_sum hf, ← b.isPos_iff]
        exact hj
      omega
  obtain ⟨k, hkpos, hkne⟩ : ∃ k, 0 < f k ∧ k ≠ i := by
    by_contra! hall
    obtain ⟨k, hkpos⟩ := (Pi.lt_def.mp hfpos).2
    have hk_eq : k = i := hall k hkpos
    subst k
    have hzero : ∀ k, k ≠ i → f k = 0 := by
      intro k hki
      have hnpos : ¬0 < f k := fun hfk ↦ hki (hall k hfk)
      exact le_antisymm (not_lt.mp hnpos) (hfpos.le k)
    have hf_eq : P.root j = f i • P.root i := by
      rw [hf, Finset.sum_eq_single_of_mem i hi]
      intro k _ hki
      rw [hzero k hki, zero_smul]
    have hdep : ¬LinearIndependent ℝ ![P.root i, P.root j] := by
      intro hli
      have hf_eq' : P.root j = (f i : ℝ) • P.root i := by
        simpa only [Int.cast_smul_eq_zsmul] using hf_eq
      have hz : (f i : ℝ) • P.root i + (-1 : ℝ) • P.root j = 0 := by
        rw [hf_eq']
        module
      have hf0 := (LinearIndependent.pair_iff.mp hli _ _ hz).1
      have hfiR : (0 : ℝ) < (f i : ℝ) := by exact_mod_cast hkpos
      linarith
    rcases IsReduced.eq_or_eq_neg i j hdep with heq | heq
    · exact hji (P.root.injective heq).symm
    · have hf_eq' : P.root j = (f i : ℝ) • P.root i := by
        simpa only [Int.cast_smul_eq_zsmul] using hf_eq
      have hsumzero : (1 : ℝ) • P.root i + (f i : ℝ) • P.root i = 0 := by
        calc
          _ = P.root i + P.root j := by rw [one_smul, hf_eq']
          _ = 0 := by rw [heq]; simp
      have hsumzero' : ((1 : ℝ) + (f i : ℝ)) • P.root i = 0 := by
        rw [add_smul]
        exact hsumzero
      have hnezero : P.root i ≠ 0 := P.ne_zero i
      have hcoef : (1 : ℝ) + (f i : ℝ) = 0 :=
        (smul_eq_zero.mp hsumzero').resolve_right hnezero
      have hfiR : (0 : ℝ) < (f i : ℝ) := by exact_mod_cast hkpos
      linarith
  have hkSupport : k ∈ b.support := hfSupport (ne_of_gt hkpos)
  let g := f + (-P.pairingIn ℤ j i) • (Pi.single (M := fun _ : ι ↦ ℤ) i 1)
  have hgSupport : g.support ⊆ b.support := by
    apply (Function.support_add f _).trans
    refine Set.union_subset_iff.mpr ⟨hfSupport, ?_⟩
    intro x hx
    by_cases hxi : x = i
    · subst x; exact hi
    · simp [hxi] at hx
  have hsum : P.root (P.reflectionPerm i j) =
      ∑ k ∈ b.support, g k • P.root k := by
    rw [P.root_reflectionPerm, P.reflection_apply_root' ℤ, hf]
    have hs : ∑ x ∈ b.support,
        ((-P.pairingIn ℤ j i) • (Pi.single (M := fun _ : ι ↦ ℤ) i 1) x) • P.root x =
        (-P.pairingIn ℤ j i) • P.root i := by
      rw [Finset.sum_eq_single_of_mem i hi]
      · simp
      · intro k _ hki
        simp [hki]
    simp only [g, Pi.add_apply, Pi.smul_apply, add_smul, Finset.sum_add_distrib]
    rw [hs]
    module
  have hgk : g k = f k := by
    dsimp only [g]
    simp [Pi.single_eq_of_ne hkne]
  have hgSign : 0 < g := by
    rcases b.pos_or_neg_of_sum_smul_root_mem g ⟨P.reflectionPerm i j, hsum⟩ hgSupport with
      hpos | hneg
    · exact hpos
    · have hle := hneg.le k
      rw [hgk] at hle
      exact ((not_le_of_gt hkpos) hle).elim
  rw [b.isPos_iff, b.height_eq_sum hsum]
  obtain ⟨l, hl⟩ := (Pi.lt_def.mp hgSign).2
  exact Finset.sum_pos' (fun k _ ↦ hgSign.le k)
    ⟨l, hgSupport (ne_of_gt hl), hl⟩


end RootPairing.Base

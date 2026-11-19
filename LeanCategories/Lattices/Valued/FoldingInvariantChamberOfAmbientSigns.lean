/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantChamberOfTwoSmulSigns
public import LeanCategories.Lattices.Valued.FoldingSignTransferLattice
public import LeanCategories.Lattices.Valued.FoldingCarrierBridge

/-!
# The folded chamber from an ambient one-sign expansion (`#116`)

The two #116 ingredients finally meet here.

* `FoldingSignTransfer.two_smul_eq_sum_smul_foldedVector`, at `M^σ`'s carrier
  (`two_smul_eq_sum_smul_foldedWallFamily`), turns a same-sign expansion of a `g`-fixed `ρ` in the
  ambient wall roots into a same-sign expansion of `2ρ` in the folded wall roots, with the scalar
  `ε ∈ {1,2}` supplied by `exists_smul_eq_add_involution`;
* `isChamberWithWalls_invariant_of_two_smul_folded_signs` consumes exactly that form.

The expansion is applied to `invariantToAmbient g ρ` (`FoldingCarrierBridge`), which is how a root
of `M^σ` is read in `L` — the coercion `(ρ : L.obj.obj.carrier)` does not elaborate, but the bridge
does.

The hypothesis that remains is the class restriction: **every root of `M^σ` is a root of `L`**
(`hsub`). On that class the ambient sign theorem — Vinberg's one-sign expansion for the wall family
of `L` — discharges the folded one-sign hypothesis, and the folded cone is a chamber. The class is
not empty: it contains the case where `M^σ` is an orthogonal summand of `L`, since then `div`
agrees. What it excludes is AEGS Lemma 3.4's type (3) — the roots of odd `T_dP`-divisibility —
which is the residual recorded in `results/issue-116-report.md`.

Source: AEGS Lemma 3.8 (**printed p. 12**) for the chamber, Definition 3.3 (**printed p. 11**) for
the fold, Lemma 3.4 (**printed pp. 11–12**) for the `ε`.

## LC-09 record

`rg "isChamberWithWalls_invariant_of"` gives the two #116 chamber theorems and nothing composing
them; `rg "ambient_signs"` gives nothing. Nothing ported.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **The folded chamber from an ambient one-sign expansion.**

`hamb` is Vinberg's expansion in the wall family `R` of `L`; `hsub` says that on this class the
roots of `M^σ`, read in `L` through `invariantToAmbient`, are roots of `L`, so the expansion is
available for each of them. The conclusion is AEGS Lemma 3.8's chamber at the folded wall set. -/
theorem isChamberWithWalls_invariant_of_ambient_signs (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    {n : ℕ} (R : Fin n → L.obj.obj.carrier) (w : involutionFixedSubmodule g)
    (hw : 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w w)
    (hroot : ∀ i, foldedWallFamily (L := L) g hg R i ∈
      negativeReflectiveRoots (invariantFixedLattice (L := L) g))
    (hwv : ∀ i, 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w
      (foldedWallFamily (L := L) g hg R i))
    (hsub : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      invariantToAmbient (L := L) g ρ ∈ negativeReflectiveRoots L)
    (hamb : ∀ ρ ∈ negativeReflectiveRoots L, ∃ c : Fin n → ℤ,
      ρ = ∑ i, c i • R i ∧ ((∀ i, 0 ≤ c i) ∨ ∀ i, c i ≤ 0)) :
    IsChamberWithWalls (invariantFixedLattice (L := L) g) (toRealForm _ w)
      (Set.range (foldedWallFamily (L := L) g hg R)) := by
  classical
  refine isChamberWithWalls_invariant_of_two_smul_folded_signs (L := L) g hg R w hw hroot hwv ?_
  intro ρ hρ
  obtain ⟨c, hc, hsignc⟩ := hamb (invariantToAmbient (L := L) g ρ) (hsub ρ hρ)
  refine ⟨fun i => c i * (if g.1 (R i) = R i then 2 else 1), ?_, ?_⟩
  · refine two_smul_eq_sum_smul_foldedWallFamily (L := L) g hg
      (fun i => if g.1 (R i) = R i then 2 else 1) (fun i => ?_) c hc
    by_cases h : g.1 (R i) = R i
    · rw [ite_eq_left h]
      exact add_apply_eq_two_smul_foldedVector (L := L) g h
    · rw [ite_eq_right h, one_zsmul]
      exact add_apply_eq_foldedVector_of_not_fixed (L := L) g h
  · rcases hsignc with h | h
    · refine Or.inl (fun i => mul_nonneg (h i) ?_)
      by_cases hi : g.1 (R i) = R i
      · rw [ite_eq_left hi]; norm_num
      · rw [ite_eq_right hi]; norm_num
    · refine Or.inr (fun i => mul_nonpos_of_nonpos_of_nonneg (h i) ?_)
      by_cases hi : g.1 (R i) = R i
      · rw [ite_eq_left hi]; norm_num
      · rw [ite_eq_right hi]; norm_num

end LeanCategories.Lattices.Valued

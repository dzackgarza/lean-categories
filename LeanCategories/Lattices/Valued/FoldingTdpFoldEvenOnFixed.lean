/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingTdpE8FoldNotRoot

/-!
# The folded `E₈` roots pair evenly with the invariant part (`#116`)

This closes the half of the `T_dP` refutation that was left as prose. `FoldingTdpE8FoldNotRoot.lean`
showed that the fold `αᵢ + Iαᵢ` is not a root of `T_dP`; to conclude that AEGS's root hypothesis
`hsub` fails there, one also needs that the fold *is* a root of the fixed lattice `M^σ`. Since the
fold has square `(−4)` (`tdpFoldedE8Root_square`), that reduces, by
`isReflectiveRoot_iff_two_dvd_pairing`, to: its pairings with the invariant part are even. That is
what this file proves.

* `tdpSwapSign_fixed_second_eq_neg_first` — an invariant vector has its second `E₈` block the
  negative of its first. This is AEGS's `I = -I_En` acting on `T_dP = U ⊥ U(2) ⊥ E₈ ⊥ E₈`,
  read off the involution in the block model.
* `tdpBlock_pairing_first_any`, `tdpBlock_pairing_second_any` — the first and second `E₈` blocks
  pair with an arbitrary vector by the `E₈` Gram matrix against that vector's block coordinates.
* `tdpFoldedE8Root_toBilin_fixed` — hence the fold pairs evenly with every invariant vector: the two
  block contributions are equal and add to twice one of them.

What is **not** done here: the statement in `M^σ` itself. Forming `invariantFixedLattice
tdpIsometry` needs `Module.Projective ℤ ↥(involutionFixedSubmodule tdpIsometry)`, which the
repository does not provide — `Module.Finite` for that submodule is not synthesizable either, so
`Module.Free` via
`Module.free_of_finite_type_torsion_free'` is not available. Closing it is a separate unit; the
mathematics that would go into it is entirely in this file.

## LC-09 record

Repository: `rg "fixed_second|pairing_first_any"` nothing; `rg "Module.Projective ℤ
↥(involutionFixedSubmodule"` gives only hypotheses, never an instance. Mathlib: no instance
`Module.Finite`/`Module.Free` for a submodule of a finite free `ℤ`-module is found by synthesis at
this pin. Corpus: nothing relevant. No port.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, *Compact moduli of Enriques surfaces of
  degree 2*, Nagoya Math. J. 259 (2025), arXiv:2312.03638v2: `T_dP = U ⊥ U(2) ⊥ E₈ ⊥ E₈` and
  `I = -I_En`, **printed pp. 12–13**; Lemma 3.4 and its converse, **printed p. 12**; the even
  2-elementary rule, **printed p. 10**.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- **An invariant vector has its second `E₈` block equal to minus its first.** -/
theorem tdpSwapSign_fixed_second_eq_neg_first {x : TdpIndex → ℤ}
    (h : tdpSwapSign x = x) (j : Fin 8) :
    x (Sum.inr (Sum.inr j)) = -x (Sum.inr (Sum.inl j)) := by
  have hj := congrFun h (Sum.inr (Sum.inr j))
  simp at hj
  linarith

/-- The first `E₈` block pairs with an arbitrary vector by the `E₈` Gram matrix. -/
theorem tdpBlock_pairing_first_any (x : Fin 8 → ℤ) (z : TdpIndex → ℤ) :
    Matrix.toBilin' tdpBlockGram (tdpFirstE8Block x) z
      = Matrix.toBilin' e8GramMatrix x (fun j => z (Sum.inr (Sum.inl j))) := by
  rw [tdpBlockGram, toBilin'_fromBlocks_zero_apply]
  have hleft : Matrix.toBilin' tdpU2Gram (fun c => tdpFirstE8Block x (Sum.inl c))
      (fun c => z (Sum.inl c)) = 0 := by
    simp [Matrix.toBilin'_apply]
  rw [hleft, zero_add, tdpE8Gram, toBilin'_fromBlocks_zero_apply]
  have hright : Matrix.toBilin' e8GramMatrix
      (fun k => tdpFirstE8Block x (Sum.inr (Sum.inr k)))
      (fun k => z (Sum.inr (Sum.inr k))) = 0 := by
    simp [Matrix.toBilin'_apply]
  rw [hright, add_zero]
  rfl

/-- The second `E₈` block pairs with an arbitrary vector by the `E₈` Gram matrix. -/
theorem tdpBlock_pairing_second_any (x : Fin 8 → ℤ) (z : TdpIndex → ℤ) :
    Matrix.toBilin' tdpBlockGram (tdpSecondE8Block x) z
      = Matrix.toBilin' e8GramMatrix x (fun j => z (Sum.inr (Sum.inr j))) := by
  rw [tdpBlockGram, toBilin'_fromBlocks_zero_apply]
  have hleft : Matrix.toBilin' tdpU2Gram (fun c => tdpSecondE8Block x (Sum.inl c))
      (fun c => z (Sum.inl c)) = 0 := by
    simp [Matrix.toBilin'_apply]
  rw [hleft, zero_add, tdpE8Gram, toBilin'_fromBlocks_zero_apply]
  have hright : Matrix.toBilin' e8GramMatrix
      (fun k => tdpSecondE8Block x (Sum.inr (Sum.inl k)))
      (fun k => z (Sum.inr (Sum.inl k))) = 0 := by
    simp [Matrix.toBilin'_apply]
  rw [hright, zero_add]
  rfl

/-- **The fold pairs evenly with every invariant vector**, stated on the Gram matrix. -/
theorem tdpFoldedE8Root_toBilin_fixed (i : Fin 8) {z : TdpIndex → ℤ}
    (hz : tdpSwapSign z = z) :
    ∃ k : ℤ,
      Matrix.toBilin' tdpBlockGram (foldedVector tdpIsometry (tdpE8Root i)) z = 2 * k := by
  refine ⟨Matrix.toBilin' e8GramMatrix (e8Basis i) (fun j => z (Sum.inr (Sum.inl j))), ?_⟩
  have hsum : foldedVector tdpIsometry (tdpE8Root i) =
      tdpFirstE8Block (e8Basis i) + tdpSecondE8Block (fun j => -e8Basis i j) := by
    rw [foldedVector_of_not_fixed tdpIsometry (tdpE8Root_not_fixed i), tdpIsometry_tdpE8Root i,
      tdpE8Root, tdpE8RootImage]
    rfl
  rw [hsum, map_add]
  simp only [LinearMap.add_apply]
  rw [tdpBlock_pairing_first_any, tdpBlock_pairing_second_any]
  have hshape : (fun j => z (Sum.inr (Sum.inr j))) = -(fun j => z (Sum.inr (Sum.inl j))) := by
    funext j
    exact tdpSwapSign_fixed_second_eq_neg_first hz j
  rw [hshape]
  have hneg : (fun j => -e8Basis i j) = -e8Basis i := rfl
  rw [hneg, map_neg, map_neg, LinearMap.neg_apply, neg_neg]
  ring

end LeanCategories.Lattices.Valued

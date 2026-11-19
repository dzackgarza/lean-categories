/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingFoldOfRoot

/-!
# Folds that are not roots: the `(−4)` case of AEGS Lemma 3.4 (`#116`)

`FoldingFoldOfRoot` proves the type (3) case: a non-fixed root orthogonal to its image folds to a
root of `M^σ`. This file proves the complementary half of AEGS's case analysis (**printed p. 12**),
the one the paper reaches with the block form: a `(−4)`-root whose image it is *not* orthogonal to
folds to a vector of **non-negative** square, and so is not a root at all.

The identity is the same one: `(α^J)² = 2α² + 2⟨α, gα⟩`. With `α² = −4` and `⟨α, gα⟩ ≥ 4` this is
`2(−4) + 2·4 = 0` at the threshold and positive beyond it. The paper obtains `⟨α, gα⟩ ≥ 4` from the
block form and divisibility ("one must have `e, e' ∈ 2E₈`, so also `e + e' ∈ 2E₈`, but then
`−(e + e')² ≥ 8`, `α · I(α) ≥ 4`"); that input is *not* reproved here — it is the hypothesis `hge`.

* `foldedVector_self_nonneg_of_square_neg_four` — the folded square is non-negative;
* `foldedWallFamily_not_mem_negativeReflectiveRoots` — hence the fold is not a negative reflective
  root of `M^σ`, i.e. `foldedRootSet`'s filter really drops it.

Together with `FoldingFoldOfRoot` this says: in the `(−4)` case, a non-fixed wall either is
orthogonal to its image (and folds to a root) or is not (and its fold has non-negative square, so is
dropped by Definition 3.7's filter). Which of the two happens is decided by the arithmetic of
`T_dP`, not by folding.

## LC-09 record

`rg "nonneg.*folded|folded.*nonneg|not_mem_negativeReflectiveRoots"` gives nothing:
`foldedRootSet`'s filter is defined but never justified in the negative direction. Nothing ported.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **The `(−4)` case of the folded-square identity**: if `α² = −4`, `α` is not fixed, and
`⟨α, gα⟩ ≥ 4`, then the fold has non-negative square. -/
theorem foldedVector_self_nonneg_of_square_neg_four (g : OrthogonalGroup L.obj)
    {α : L.obj.obj.carrier} (h4 : L.obj.obj.pairing α α = -4)
    (hge : 4 ≤ L.obj.obj.pairing α (g.1 α)) (hne : g.1 α ≠ α) :
    0 ≤ L.obj.obj.pairing (foldedVector g α) (foldedVector g α) := by
  rw [pairing_folded_self_of_not_fixed g hne, h4]
  linarith

/-- **Such a fold is not a negative reflective root**: Definition 3.7's filter drops it. -/
theorem foldedWallFamily_not_mem_negativeReflectiveRoots (g : OrthogonalGroup L.obj)
    (hg : g * g = 1) [Module.Projective ℤ (involutionFixedSubmodule g)]
    {α : L.obj.obj.carrier} (h4 : L.obj.obj.pairing α α = -4)
    (hge : 4 ≤ L.obj.obj.pairing α (g.1 α)) (hne : g.1 α ≠ α) :
    (⟨foldedVector g α, foldedVector_mem_fixed g hg α⟩ : involutionFixedSubmodule g) ∉
      negativeReflectiveRoots (invariantFixedLattice (L := L) g) := by
  intro hmem
  have hsq := hmem.2
  have hcoe : (invariantFixedLattice (L := L) g).obj.obj.pairing
      (⟨foldedVector g α, foldedVector_mem_fixed g hg α⟩ : involutionFixedSubmodule g)
      (⟨foldedVector g α, foldedVector_mem_fixed g hg α⟩ : involutionFixedSubmodule g)
      = L.obj.obj.pairing (foldedVector g α) (foldedVector g α) := rfl
  rw [hcoe] at hsq
  have hnn := foldedVector_self_nonneg_of_square_neg_four (L := L) g h4 hge hne
  linarith

end LeanCategories.Lattices.Valued

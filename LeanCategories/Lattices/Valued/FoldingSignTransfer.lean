/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.Folding

/-!
# Folding a same-sign combination of wall roots (`#116`)

The chamber theorem for the folded lattice consumes a one-sign expansion of every root of `M^σ`
in the *folded* wall roots
(`FoldingInvariantChamberOfSigns.isChamberWithWalls_invariant_of_folded_signs`).
This file supplies the half of that which folding itself gives: a root of `M^σ` that is also a root
of `L`, written as a same-sign combination of the ambient wall roots, folds to a same-sign
combination of the folds.

The identity is one line of bilinearity. For `g`-fixed `ρ` and `ρ = Σ cᵢRᵢ`,

  `2ρ = ρ + gρ = Σ cᵢ (Rᵢ + gRᵢ)`,

and `Rᵢ + gRᵢ` is `2·Rᵢ^g` when `Rᵢ` is fixed and `Rᵢ^g` otherwise. So the folded coefficients are
`2cᵢ` or `cᵢ` — same sign as `cᵢ`, and the factor `2` on the left is the only price of staying over
`ℤ`: the coefficient `cᵢ/2` would not be integral, and this is exactly the `ε` that the real-form
version of the identity (`realForm_pairing_folded_of_not_fixed`, `Folding.lean`) hides in its proof.

* `add_apply_eq_two_smul_foldedVector` — at a fixed vector, `x + gx` is twice the fold;
* `add_apply_eq_foldedVector_of_not_fixed` — at a non-fixed vector, `x + gx` *is* the fold;
* `two_smul_eq_sum_smul_foldedVector` — a same-sign combination of walls, doubled, folds to a
  same-sign combination of the folds, with the coefficients `cᵢ εᵢ`.

No source to cite for the statements: the fold is AEGS Definition 3.3 (**printed p. 11**) and the
chamber is Lemma 3.8 (**printed p. 12**); the algebra is the `ε ∈ {1,2}` that the paper's proof of
Lemma 3.4 (**printed p. 12**) uses silently when it writes `α^J = α + I(α)`.

## LC-09 record

`rg "foldedVector_of_fixed|foldedVector_of_not_fixed"` gives the two case lemmas and the real-form
pairing identity `realForm_pairing_folded_of_not_fixed`/`..._of_fixed` (`Folding.lean`), which carry
the same `ε` at the level of pairings; no statement about the *sum* `x + g x` existed.
`rg "sameSign|oneSign"` in Mathlib gives only `RootPairing.Base`'s one-sign field. Nothing ported.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **At a fixed vector, `x + g x` is twice the fold.** -/
theorem add_apply_eq_two_smul_foldedVector (g : OrthogonalGroup L.obj) {x : L.obj.obj.carrier}
    (hx : g.1 x = x) : x + g.1 x = (2 : ℤ) • foldedVector g x := by
  have h2 : (2 : ℤ) • x = x + x := by
    rw [show (2 : ℤ) = 1 + 1 from rfl, add_zsmul, one_zsmul]
  rw [foldedVector_of_fixed g hx, h2, hx]

/-- **At a non-fixed vector, `x + g x` *is* the fold.** -/
theorem add_apply_eq_foldedVector_of_not_fixed (g : OrthogonalGroup L.obj)
    {x : L.obj.obj.carrier} (hx : g.1 x ≠ x) : x + g.1 x = foldedVector g x := by
  rw [foldedVector_of_not_fixed g hx]

/-- **A same-sign combination of wall roots, doubled, is a same-sign combination of the folds.**

If `ρ` is fixed by `g` and `ρ = Σ cᵢ Rᵢ`, and `ε` is a family with `Rᵢ + gRᵢ = εᵢ • Rᵢ^g` (which is
`2` at a fixed wall and `1` at a non-fixed one, the two lemmas above), then

  `2ρ = Σ (cᵢ εᵢ) • Rᵢ^g`.

The coefficients keep the sign of the `cᵢ`; the factor `2` on the left is why the one-sign
hypothesis of the chamber theorem is stated on the folds and not read off the ambient chamber. -/
theorem two_smul_eq_sum_smul_foldedVector (g : OrthogonalGroup L.obj)
    {n : ℕ} {R : Fin n → L.obj.obj.carrier} {ρ : L.obj.obj.carrier} (hρ : g.1 ρ = ρ)
    (ε : Fin n → ℤ) (hε : ∀ i, R i + g.1 (R i) = ε i • foldedVector g (R i))
    (c : Fin n → ℤ) (hc : ρ = ∑ i, c i • R i) :
    (2 : ℤ) • ρ = ∑ i, (c i * ε i) • foldedVector g (R i) := by
  have hmap : g.1 ρ = ∑ i, c i • g.1 (R i) := by
    rw [hc, map_sum]
    exact Finset.sum_congr rfl (fun i _ => map_zsmul (g.1) (c i) (R i))
  have h2 : (2 : ℤ) • ρ = ρ + g.1 ρ := by
    rw [show (2 : ℤ) = 1 + 1 from rfl, add_zsmul, one_zsmul, hρ]
  calc (2 : ℤ) • ρ = ρ + g.1 ρ := h2
    _ = (∑ i, c i • R i) + ∑ i, c i • g.1 (R i) := by rw [hmap, hc]
    _ = ∑ i, (c i • R i + c i • g.1 (R i)) := Finset.sum_add_distrib.symm
    _ = ∑ i, (c i * ε i) • foldedVector g (R i) :=
      Finset.sum_congr rfl (fun i _ =>
        (zsmul_add (R i) (g.1 (R i)) (c i)).symm.trans
          ((congrArg (fun y => c i • y) (hε i)).trans
            (mul_zsmul (foldedVector g (R i)) (c i) (ε i)).symm))

end LeanCategories.Lattices.Valued

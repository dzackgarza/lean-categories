/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingTdpE8NoFoldDropped

/-!
# The `E₈` family is not a chamber of `T_dP` (`#116`)

`chamberOf_folded_trace_tdpE8` (`FoldingTdpE8NoFoldDropped.lean`) carries
`IsChamberWithWalls tdpFiniteLattice t (Set.range tdpE8Family)`. That hypothesis is **false**, and
this file proves it: `T_dP = U ⊥ U(2) ⊥ E₈ ⊥ E₈` has a `U` summand orthogonal to both `E₈` summands,
so its `(−2)`-root cannot be a `ℤ`-combination of the eight folded `E₈` walls, while a chamber's
wall set must span the negative reflective roots in one-sign combinations.

* `tdpURoot` — the root `(1, -1)` of the `U` summand;
* `tdpURoot_square` — it has square `(-2)`, so it is a negative reflective root of `T_dP`;
* `tdpURoot_pairing_fold` — it is orthogonal to every folded `E₈` root;
* `tdpURoot_not_combination` — hence it is **not** a `ℤ`-combination of them.

So the chamber hypothesis at the eight-wall family is vacuous, and `chamberOf_folded_trace_tdpE8` is
not an instance of AEGS Lemma 3.8 for `T_dP`: that needs the full wall set of the printed chamber
(Figure 5, **printed p. 11**), not the `E₈` block alone. The trace identity itself remains true — it
is an implication — but this is the reason it cannot be read as a statement about `T_dP`'s chamber.

## LC-09 record

Queries run before writing: `"chamber wall set spans roots"` and `"hyperbolic lattice chamber
generators"`; see the shell record in the commit message. Nothing in the repository or Mathlib
states that a proper subset of a chamber's walls fails to generate; the argument here is from the
printed block decomposition.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, *Compact moduli of Enriques surfaces of degree
  2*,
  Nagoya Math. J. 259 (2025), arXiv:2312.03638v2: `T_dP = U ⊥ U(2) ⊥ E₈ ⊥ E₈` and `I = -I_En`
  **printed pp. 12–13**; Figure 5's chamber **printed p. 11**; Definition 3.7 and Lemma 3.8
  **printed p. 12**.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The `U` summand of `T_dP`, as a vector of the whole lattice. -/
def tdpUBlock (x : Fin 2 → ℤ) : TdpIndex → ℤ :=
  Sum.elim (Sum.elim x (fun _ => 0)) (Sum.elim (fun _ => 0) (fun _ => 0))

/-- The root `(1, -1)` of the `U` summand. -/
def tdpURoot : TdpIndex → ℤ := tdpUBlock (fun c => if c = 0 then 1 else -1)

/-- **The `U`-root has square `(-2)`.** -/
theorem tdpURoot_square :
    tdpFiniteLattice.obj.obj.pairing tdpURoot tdpURoot = -2 := by
  change Matrix.toBilin' tdpBlockGram tdpURoot tdpURoot = -2
  rw [tdpBlockGram, toBilin'_fromBlocks_zero_apply, tdpU2Gram,
    toBilin'_fromBlocks_zero_apply]
  simp [tdpURoot, tdpUBlock, hyperbolicPlaneGramMatrix, Matrix.toBilin'_apply,
    Fin.sum_univ_two]

/-- **The `U`-root is orthogonal to every folded `E₈` root**: the summands are orthogonal. -/
theorem tdpURoot_pairing_fold (i : Fin 8) :
    tdpFiniteLattice.obj.obj.pairing tdpURoot (foldedVector tdpIsometry (tdpE8Root i)) = 0 := by
  rw [foldedVector_of_not_fixed tdpIsometry (tdpE8Root_not_fixed i), tdpIsometry_tdpE8Root i,
    tdpE8Root, tdpE8RootImage]
  change Matrix.toBilin' tdpBlockGram tdpURoot
    (tdpFirstE8Block (e8Basis i) + tdpSecondE8Block (fun j => -e8Basis i j)) = 0
  rw [tdpBlockGram, toBilin'_fromBlocks_zero_apply]
  simp [tdpU2Gram, tdpE8Gram, tdpURoot, tdpUBlock, tdpFirstE8Block, tdpSecondE8Block,
    Matrix.toBilin'_apply]

/-- **The `U`-root is not a `ℤ`-combination of the eight folded `E₈` walls** — so the eight-wall
family is not a chamber of `T_dP`, and the chamber hypothesis of `chamberOf_folded_trace_tdpE8` is
vacuous. -/
theorem tdpURoot_not_combination :
    ¬ ∃ c : Fin 8 → ℤ,
        tdpURoot = ∑ i, c i • foldedVector tdpIsometry (tdpE8Root i) := by
  rintro ⟨c, hc⟩
  have hzero : tdpFiniteLattice.obj.obj.adjoint tdpURoot
      (∑ i, c i • foldedVector tdpIsometry (tdpE8Root i)) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [map_smul]
    have h : tdpFiniteLattice.obj.obj.adjoint tdpURoot
        (foldedVector tdpIsometry (tdpE8Root i)) = 0 := tdpURoot_pairing_fold i
    rw [h, smul_zero]
  rw [← hc] at hzero
  have hsq : tdpFiniteLattice.obj.obj.adjoint tdpURoot tdpURoot = -2 := tdpURoot_square
  rw [hsq] at hzero
  exact absurd hzero (by norm_num)

end LeanCategories.Lattices.Valued

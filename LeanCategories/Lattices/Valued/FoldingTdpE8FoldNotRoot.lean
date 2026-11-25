/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingDiagram
public import LeanCategories.Lattices.Valued.FoldingNegativeFourRoots

/-!
# The folded `E₈` root of `T_dP` is not a root of `T_dP` (`#116`)

AEGS, **printed p. 12**, distinguish the two lattices by the divisibility of a folded root: after
Lemma 3.4, "`div(α^I) ≠ 2` in `T_dP`, `= 2` in `T_En`". The type (3) case is precisely a `(−4)`-root
whose ambient pairings are not all even.

This file machine-checks that statement in the block model of `T_dP` built in `FoldingDiagram.lean`
(`T_dP = U ⊥ U(2) ⊥ E₈ ⊥ E₈`, with `I` negating and swapping the two `E₈` summands). The fold of the
`i`-th `E₈` simple root is `αᵢ + Iαᵢ`, and pairing it with the *first-block* vector `αⱼ` leaves
exactly the `E₈` Gram entry:

* `tdpFoldedE8Root_pairing_single` — `⟨αᵢ + Iαᵢ, αⱼ⟩ = (e8GramMatrix i j)`;
* `tdpFoldedE8Root_pairing_zero_two` — the entry `(0, 2)` is `1`, which is odd;
* `tdpFoldedE8Root_not_two_dvd` — so the fold has an odd ambient pairing;
* `tdpFoldedE8Root_not_isReflectiveRoot` — and therefore, since its square is `(−4)`
  (`tdpFoldedE8Root_square`), it is **not a reflective root of `T_dP`**;
* `tdpFoldedE8Root_not_mem_negativeReflectiveRoots` — so it is not a root of `T_dP` at all.

Consequence for the chamber theorem. `hsub` asks that the ambient image of *every* root of `M^σ`
be a root of `L`. The vector above is the fold of a wall root, hence a member of
`negativeReflectiveRoots` of the fixed lattice once the per-wall conditions hold
(`foldedWallFamily_mem_negativeReflectiveRoots`,
`FoldingRootHypothesis.lean`, AEGS Lemma 3.4 forward, **printed pp. 11–12**), while by
`invariantCarrierToAmbient_foldedWallFamily` its ambient image is the fold itself — which is not a
root of `L`. So for the `T_dP` folding `hsub` is **false**, and with it `hsq`; the two are
equivalent by `hsub_iff_hsq_of_two_elementary` (`FoldingRootTransferEquivalence.lean`). The theorem
is therefore
not applicable in the `T_dP` direction, only where the folds *are* roots — which is the content of
the `T_En` half of the source's dichotomy. This is not a defect of the formalization: it is the
source's own `div(α^I) ≠ 2`.

Nothing here says anything about `T_En`; that would need the other block's arithmetic.

## LC-09 record

Repository: `rg "div"` over `Lattices/Valued/Folding*` gives only `dvd_two_mul` uses in
`FoldingNegative*Roots`; no statement that a folded root fails to be a root, and no use of the
`(0,2)` Gram entry. Mathlib: `LinearMap.IsReflective` only in
`LinearAlgebra/RootSystem/OfBilinear.lean`. Corpus: nothing for `"reflectiveRoot invariant"` or
`"IsReflective sublattice"`; no port.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, *Compact moduli of Enriques surfaces of degree
  2*,
  Nagoya Math. J. 259 (2025), arXiv:2312.03638v2: roots, the root criterion `2 div(α) ∈ (α·α)ℤ`, the
  even 2-elementary rule, **printed p. 10**; Lemma 3.4 with the `div(α^I) ≠ 2` / `= 2` dichotomy,
  **printed p. 12**; Lemma 3.9 and Figures 7–8, **printed pp. 13–14**.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, 2.13, 2.15, as
  cited by the source at **printed p. 12**.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- **The fold pairs with the first `E₈` block by the `E₈` Gram entry**: `⟨αᵢ + Iαᵢ, αⱼ⟩ = gᵢⱼ`. -/
theorem tdpFoldedE8Root_pairing_single (i j : Fin 8) :
    tdpFiniteLattice.obj.obj.pairing (foldedVector tdpIsometry (tdpE8Root i)) (tdpE8Root j)
      = e8GramMatrix i j := by
  rw [foldedVector_of_not_fixed tdpIsometry (tdpE8Root_not_fixed i), tdpIsometry_tdpE8Root i]
  have h1 : tdpFiniteLattice.obj.obj.pairing (tdpE8Root i) (tdpE8Root j) = e8GramMatrix i j := by
    rw [tdpE8Root, tdpE8Root, tdpBlock_pairing_first_first, e8Basis_pairing]
  have h2 : tdpFiniteLattice.obj.obj.pairing (tdpE8RootImage i) (tdpE8Root j) = 0 := by
    rw [tdpE8RootImage, tdpE8Root, tdpBlock_pairing_second_first]
  rw [BilinModuleCat.pairing_add_left, h1, h2, add_zero]

/-- The `(0,2)` entry of the `E₈` Gram matrix is `1`: the two simple roots are adjacent. -/
theorem tdpFoldedE8Root_pairing_zero_two :
    tdpFiniteLattice.obj.obj.pairing (foldedVector tdpIsometry (tdpE8Root 0)) (tdpE8Root 2)
      = 1 := by
  rw [tdpFoldedE8Root_pairing_single, e8GramMatrix_eq]
  decide

/-- **The fold has an odd ambient pairing**, so `div` is not `2`. -/
theorem tdpFoldedE8Root_not_two_dvd :
    ¬ ∀ y : tdpFiniteLattice.obj.obj.carrier,
        (2 : ℤ) ∣ tdpFiniteLattice.obj.obj.pairing
          (foldedVector tdpIsometry (tdpE8Root 0)) y := by
  intro h
  have h1 := h (tdpE8Root 2)
  rw [tdpFoldedE8Root_pairing_zero_two] at h1
  norm_num at h1

/-- **The folded `E₈` root is not a root of `T_dP`** — AEGS p. 12's `div(α^I) ≠ 2`, case (3). -/
theorem tdpFoldedE8Root_not_isReflectiveRoot :
    ¬ IsReflectiveRoot tdpFiniteLattice.obj (foldedVector tdpIsometry (tdpE8Root 0)) := by
  intro h
  exact tdpFoldedE8Root_not_two_dvd
    ((isReflectiveRoot_iff_two_dvd_pairing (tdpFoldedE8Root_square 0)).mp h)

/-- Hence the fold is not among the roots of `T_dP`. -/
theorem tdpFoldedE8Root_not_mem_negativeReflectiveRoots :
    foldedVector tdpIsometry (tdpE8Root 0) ∉ negativeReflectiveRoots tdpFiniteLattice := by
  intro h
  exact tdpFoldedE8Root_not_isReflectiveRoot h.1

end LeanCategories.Lattices.Valued

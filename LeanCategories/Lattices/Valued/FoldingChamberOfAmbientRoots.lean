/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingChamberOfDefinition37
public import LeanCategories.Lattices.Valued.FoldingNegativeTwoRoots

/-!
# The folded chamber without the classification input (`#116`)

`isChamberWithWalls_invariant_of_foldedRootSet` carries two external inputs. One is Vinberg's
same-sign expansion (`hamb`). The other is `hsq`: every root of `M^σ` is `(−2)`, or `(−4)` with all
ambient pairings even. AEGS obtain that from Namikawa's classification of `O(T_En)`-orbits of
`(−2)`- and `(−4)`-vectors, cited at **printed p. 12** (Lemma 3.4's converse, [Nam85, 2.13 and
2.15]).

What the chain actually uses `hsq` for is one thing: to know that a root `ρ` of `M^σ`, read in `L`
through `invariantCarrierToAmbient`, is a root of `L`. That is `hsub`, and it is already the
hypothesis of `isChamberWithWalls_invariant_of_ambient_signs`
(`FoldingInvariantChamberOfAmbientSigns.lean:63`); `hsq` enters only as a sufficient condition for
it
(`isChamberWithWalls_invariant_of_square_criterion`).

This file states the theorem at `hsub`, which is weaker than `hsq` and checkable one root at a time,
and then records the case in which `hsub` costs nothing at all:

* `isChamberWithWalls_invariant_of_wall_data_hsub` — the assembled theorem with `hsub` for `hsq`;
* `isChamberWithWalls_invariant_of_foldedRootSet_of_hsub` — the same at Definition 3.7's folded root
  set (**printed p. 12**), i.e. AEGS Lemma 3.8's object;
* `isChamberWithWalls_invariant_of_foldedRootSet_of_square_neg_two` — the **white** case: when every
  root of `M^σ` is a `(−2)`-vector, `hsub` is
  `isReflectiveRoot_invariantCarrierToAmbient_of_square_neg_two`
  applied root by root, so **no classification input remains**. AEGS colour the roots by square,
  white for `α² = −2` and black for `α² = −4`, and state that for these lattices the roots are the
  `(−2)`-vectors and the `(−4)`-vectors with `div(α) = 2` (**printed p. 10**); the theorem below is
  the case in which the folded diagram has no black vertex.

The black case is not covered: a `(−4)`-root of `M^σ` is a root of `L` only when its ambient
pairings
are even (`isReflectiveRoot_invariantCarrierToAmbient_iff_two_dvd_pairing`), and nothing in the
folding argument decides that. The paper decides it by the classification, which is why `hsq` is
still the hypothesis of the previous module's headline statement.

## LC-09 record

Queries: `rg "hsub"` over the repository gives unrelated local hypotheses (`MooreSpaceExactness`,
`AugmentedObjects`, `JordanSplitting`), never a root-transfer statement; `rg
"mem_negativeReflectiveRoots.*invariantCarrier"` gives only the two `FoldingNegative*Roots` lemmas
this file calls. Mathlib: `LinearMap.IsReflective` occurs only in
`Mathlib/LinearAlgebra/RootSystem/OfBilinear.lean`, which has no sublattice or fixed-part transfer.
Formalization corpus (live API, `scripts/formalization_corpus.py`): `"IsReflective sublattice"` and
`"reflectiveRoot invariant"` return nothing; `"two-elementary"` returns
`TauCeti/LinearAlgebra/IntegralLattice/TwoElementary.lean` and
`TauCeti/LinearAlgebra/FiniteBilinearModule/Dyadic/TwoElementary.lean`. Those are the right notion
for the *black* case, but they are stated for TauCeti's own finite quadratic and integral-lattice
frameworks, not for the bundled `FiniteProjectiveLatticeCat` carrier used here, and they classify
discriminant forms rather than transfer reflectivity to an ambient lattice; nothing is ported. They
are the lead for the `(−4)` half, not for this file.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, *Compact moduli of Enriques surfaces of degree
  2*,
  Nagoya Math. J. 259 (2025), arXiv:2312.03638v2: Definition 3.7 and Lemma 3.8, **printed p. 12**;
  roots, the white/black colouring and the `(−2)`/`(−4)` rule, **printed p. 10**.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, 2.13, 2.15, as
  cited by the source at **printed p. 12**.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **The assembled chamber theorem with the classification input replaced by its use.**

`hsq` appears in `isChamberWithWalls_invariant_of_wall_data'` only to produce `hsub`; here `hsub` is
asked for directly, one divisibility check per root instead of a classification of root orbits. -/
theorem isChamberWithWalls_invariant_of_wall_data_hsub (g : OrthogonalGroup L.obj)
    (hg : g * g = 1) [Module.Projective ℤ (involutionFixedSubmodule g)]
    {n : ℕ} (R : Fin n → L.obj.obj.carrier) (w : involutionFixedSubmodule g)
    (hw : 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w w)
    (hwamb : ∀ i, 0 < L.obj.obj.pairing (w : L.obj.obj.carrier) (R i))
    (hR : ∀ i, IsReflectiveRoot L.obj (R i))
    (hneg : ∀ i, L.obj.obj.pairing (R i) (R i) < 0)
    (hcase : ∀ i, g.1 (R i) = R i ∨ L.obj.obj.pairing (R i) (g.1 (R i)) = 0)
    (hsub : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      invariantCarrierToAmbient (L := L) g ρ ∈ negativeReflectiveRoots L)
    (hamb : ∀ ρ ∈ negativeReflectiveRoots L, ∃ c : Fin n → ℤ,
      ρ = ∑ i, c i • R i ∧ ((∀ i, 0 ≤ c i) ∨ ∀ i, c i ≤ 0)) :
    IsChamberWithWalls (invariantFixedLattice (L := L) g) (toRealForm _ w)
      (Set.range (foldedWallFamily (L := L) g hg R)) :=
  isChamberWithWalls_invariant_of_ambient_signs (L := L) g hg R w hw
    (foldedWallFamily_mem_negativeReflectiveRoots (L := L) g hg R hR hneg hcase)
    (foldedWallFamily_pairing_pos (L := L) g hg R w hwamb) hsub hamb

/-- **AEGS Lemma 3.8 at Definition 3.7's object**, with `hsub` in place of `hsq`. -/
theorem isChamberWithWalls_invariant_of_foldedRootSet_of_hsub (g : OrthogonalGroup L.obj)
    (hg : g * g = 1) [Module.Projective ℤ (involutionFixedSubmodule g)]
    {n : ℕ} (R : Fin n → L.obj.obj.carrier) (w : involutionFixedSubmodule g)
    (hw : 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w w)
    (hwamb : ∀ i, 0 < L.obj.obj.pairing (w : L.obj.obj.carrier) (R i))
    (hR : ∀ i, IsReflectiveRoot L.obj (R i))
    (hneg : ∀ i, L.obj.obj.pairing (R i) (R i) < 0)
    (hcase : ∀ i, g.1 (R i) = R i ∨ L.obj.obj.pairing (R i) (g.1 (R i)) = 0)
    (hsub : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      invariantCarrierToAmbient (L := L) g ρ ∈ negativeReflectiveRoots L)
    (hamb : ∀ ρ ∈ negativeReflectiveRoots L, ∃ c : Fin n → ℤ,
      ρ = ∑ i, c i • R i ∧ ((∀ i, 0 ≤ c i) ∨ ∀ i, c i ≤ 0)) :
    IsChamberWithWalls (invariantFixedLattice (L := L) g) (toRealForm _ w)
      (foldedRootSet (L := L) g (Set.range R)) := by
  rw [← range_foldedWallFamily_eq_foldedRootSet (L := L) g hg R
    (foldedWallFamily_mem_negativeReflectiveRoots (L := L) g hg R hR hneg hcase)]
  exact isChamberWithWalls_invariant_of_wall_data_hsub (L := L) g hg R w hw hwamb hR hneg hcase
    hsub hamb

/-- **The white case: no classification input.**

When every root of `M^σ` is a `(−2)`-vector — AEGS's white vertices (**printed p. 10**) — the
ambient
image of a root is a root of `L` by `isReflectiveRoot_invariantCarrierToAmbient_of_square_neg_two`,
so
`hsq` and with it Namikawa's classification drop out of the statement entirely. -/
theorem isChamberWithWalls_invariant_of_foldedRootSet_of_square_neg_two
    (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    {n : ℕ} (R : Fin n → L.obj.obj.carrier) (w : involutionFixedSubmodule g)
    (hw : 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w w)
    (hwamb : ∀ i, 0 < L.obj.obj.pairing (w : L.obj.obj.carrier) (R i))
    (hR : ∀ i, IsReflectiveRoot L.obj (R i))
    (hneg : ∀ i, L.obj.obj.pairing (R i) (R i) < 0)
    (hcase : ∀ i, g.1 (R i) = R i ∨ L.obj.obj.pairing (R i) (g.1 (R i)) = 0)
    (h2 : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ = -2)
    (hamb : ∀ ρ ∈ negativeReflectiveRoots L, ∃ c : Fin n → ℤ,
      ρ = ∑ i, c i • R i ∧ ((∀ i, 0 ≤ c i) ∨ ∀ i, c i ≤ 0)) :
    IsChamberWithWalls (invariantFixedLattice (L := L) g) (toRealForm _ w)
      (foldedRootSet (L := L) g (Set.range R)) := by
  refine isChamberWithWalls_invariant_of_foldedRootSet_of_hsub (L := L) g hg R w hw hwamb hR hneg
    hcase ?_ hamb
  intro ρ hρ
  refine ⟨isReflectiveRoot_invariantCarrierToAmbient_of_square_neg_two (L := L) g (h2 ρ hρ), ?_⟩
  have hcoe : L.obj.obj.pairing (invariantCarrierToAmbient (L := L) g ρ)
      (invariantCarrierToAmbient (L := L) g ρ)
      = (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ := by
    rw [invariantCarrierToAmbient_apply]
    exact (invariantFixedLattice_pairing (L := L) g
      (show ↥(involutionFixedSubmodule g) from ρ)
      (show ↥(involutionFixedSubmodule g) from ρ)).symm
  rw [hcoe, h2 ρ hρ]
  norm_num

end LeanCategories.Lattices.Valued

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantChamberOfAmbientSigns
public import LeanCategories.Lattices.Valued.FoldingNegativeFourRoots

/-!
# The class restriction, in checkable form (`#116`)

`isChamberWithWalls_invariant_of_ambient_signs` assumes `hsub`: every root of `M^σ`, read in `L`
through the carrier bridge, is a root of `L`. That is a statement about reflectivity of roots one
has to know individually. This file replaces it by the criterion the last two commits prove:

* a root of square `−2` is **always** a root of `L`
  (`isReflectiveRoot_invariantCarrierToAmbient_of_square_neg_two`);
* a root of square `−4` is one **iff** all its ambient pairings are even
  (`isReflectiveRoot_invariantCarrierToAmbient_iff_two_dvd_pairing`).

So on a lattice whose roots have square `−2` or `−4` — the even 2-elementary case, which is AEGS's
setting (**printed p. 10**: "the roots are the `(−2)`-vectors and the `(−4)`-vectors with
`div(α) = 2`") — the restriction becomes a vector-by-vector computation:

  every root is `(−2)`, or `(−4)` with even pairings.

What the paper still supplies and this does not is that the second alternative *holds* for the
`(−4)`-roots, which is Namikawa's orbit classification (Lemma 3.4's converse, **printed p. 12**).

* `isChamberWithWalls_invariant_of_square_criterion` — the chamber, with the restriction in the
  checkable form.

## LC-09 record

`rg "square_criterion|hsqrt|two_dvd"` gives the two preceding #116 modules and nothing combining
them into the chamber theorem's hypothesis. Nothing ported.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **The folded chamber, with the class restriction in checkable form.**

Instead of asserting reflectivity of each root of `M^σ` in `L` (`hsub`), it is enough to know that
each root has square `−2`, or square `−4` with all ambient pairings even. The first is automatic and
the second is a divisibility computation. -/
theorem isChamberWithWalls_invariant_of_square_criterion (g : OrthogonalGroup L.obj)
    (hg : g * g = 1) [Module.Projective ℤ (involutionFixedSubmodule g)]
    {n : ℕ} (R : Fin n → L.obj.obj.carrier) (w : involutionFixedSubmodule g)
    (hw : 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w w)
    (hroot : ∀ i, foldedWallFamily (L := L) g hg R i ∈
      negativeReflectiveRoots (invariantFixedLattice (L := L) g))
    (hwv : ∀ i, 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w
      (foldedWallFamily (L := L) g hg R i))
    (hsq : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ = -2 ∨
        ((invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ = -4 ∧
          ∀ y : L.obj.obj.carrier,
            (2 : ℤ) ∣ L.obj.obj.pairing (invariantCarrierToAmbient (L := L) g ρ) y))
    (hamb : ∀ ρ ∈ negativeReflectiveRoots L, ∃ c : Fin n → ℤ,
      ρ = ∑ i, c i • R i ∧ ((∀ i, 0 ≤ c i) ∨ ∀ i, c i ≤ 0)) :
    IsChamberWithWalls (invariantFixedLattice (L := L) g) (toRealForm _ w)
      (Set.range (foldedWallFamily (L := L) g hg R)) := by
  refine isChamberWithWalls_invariant_of_ambient_signs (L := L) g hg R w hw hroot hwv ?_ hamb
  intro ρ hρ
  have hcoe : L.obj.obj.pairing (invariantCarrierToAmbient (L := L) g ρ)
      (invariantCarrierToAmbient (L := L) g ρ)
      = (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ := by
    rw [invariantCarrierToAmbient_apply]
    exact (invariantFixedLattice_pairing (L := L) g
      (show ↥(involutionFixedSubmodule g) from ρ)
      (show ↥(involutionFixedSubmodule g) from ρ)).symm
  have hneg : L.obj.obj.pairing (invariantCarrierToAmbient (L := L) g ρ)
      (invariantCarrierToAmbient (L := L) g ρ) < 0 := by
    rw [hcoe]
    rcases hsq ρ hρ with h2 | ⟨h4, _⟩
    · rw [h2]; norm_num
    · rw [h4]; norm_num
  refine ⟨?_, hneg⟩
  rcases hsq ρ hρ with h2 | ⟨h4, hev⟩
  · exact isReflectiveRoot_invariantCarrierToAmbient_of_square_neg_two (L := L) g h2
  · exact (isReflectiveRoot_invariantCarrierToAmbient_iff_two_dvd_pairing (L := L) g h4).mpr hev

end LeanCategories.Lattices.Valued

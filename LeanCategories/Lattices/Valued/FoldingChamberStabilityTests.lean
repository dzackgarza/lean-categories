/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingChamberStability

/-!
# Probes for `FoldingChamberStability`, on the smallest input that decides it

`realFormOrthogonalHom_mem_rootInteriorCone` derives the `hstab` hypothesis of
`isChamberWithWalls_invariant_of_chamber` from a diagram involution. Two things need checking and
neither needs a chamber:

* the statement is not vacuous — it is applied at the identity involution of `E₁₀(2)`'s wall
  family, where `ActsThrough` holds through `id` and the hypothesis `g t = t` holds because `g = 1`;
* the hypotheses are the ones a diagram involution gives, not the conclusion: `ActsThrough` is a
  statement about the *roots*, and `hπ` about the *permutation*, and neither mentions the cone.

The axiom footprint is checked too.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

example {L : FiniteProjectiveLatticeCat ℤ ℤ} {ι : Type*} (r : ι → L.obj.obj.carrier)
    {t z : (realForm L).obj.carrier}
    (hz : z ∈ rootInteriorCone L t (Set.range r)) :
    realFormOrthogonalHom L (1 : OrthogonalGroup L.obj) z ∈
      rootInteriorCone L t (Set.range r) :=
  realFormOrthogonalHom_mem_rootInteriorCone (L := L)
    (g := (1 : OrthogonalGroup L.obj)) (r := r) (π := id)
    (fun _ => rfl) (actsThrough_one r) (by rw [map_one]; rfl) hz

#print axioms realFormOrthogonalHom_mem_rootInteriorCone

end LeanCategories.Lattices.Valued

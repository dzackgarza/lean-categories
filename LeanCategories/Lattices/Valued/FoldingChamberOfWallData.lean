/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingRootHypothesis
public import LeanCategories.Lattices.Valued.FoldingChamberOfSquareCriterion

/-!
# The folded chamber, from diagram-level data (`#116`)

This is the end of the #116 chain: one statement whose hypotheses are exactly the inputs the paper
supplies and the development cannot prove, with everything folding does discharged along the way.

Where each hypothesis comes from:

* `hw`, `hwv` (an interior vector of the folded cone): Lemma 3.8's maximal-dimension hypothesis
  (**printed p. 12**), realized by `exists_mem_fixedPart_interior` under `hstab`;
* `hR`, `hneg` (wall roots reflective, of negative square): the diagram of `L`, Figure 5
  (**printed p. 11**);
* `hcase` (each wall fixed or orthogonal to its image): the arithmetic of `T_dP`, per wall
  (**printed p. 12**);
* `hsq` (roots of `M^σ` are `(−2)`, or `(−4)` with even pairings): Namikawa, via Lemma 3.4's
  converse (**printed p. 12**);
* `hamb` (roots of `L` are same-sign combinations of the walls): Vinberg's one-sign expansion, a
  chamber/Tits-cone theorem.

The first three are checkable on the diagrams; the last two are the external inputs. What is *not*
a hypothesis any more: `hcomplete`, the sign covering, the carrier identification, and `hroot`.

* `isChamberWithWalls_invariant_of_wall_data` — the chamber.

## LC-09 record

`rg "of_wall_data|wall_data"` gives nothing; the chamber theorems of the #116 chain are the five
already cited, and this composes the last two. Nothing ported.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **The folded chamber, from diagram-level data.**

Every hypothesis is either diagram-level (`hR`, `hneg`, `hcase`, `hw`, `hwv`) or one of the two
inputs the paper takes from outside folding (`hsq` from Namikawa, `hamb` from Vinberg). The
conclusion is AEGS Lemma 3.8's chamber at the folded wall set. -/
theorem isChamberWithWalls_invariant_of_wall_data (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    {n : ℕ} (R : Fin n → L.obj.obj.carrier) (w : involutionFixedSubmodule g)
    (hw : 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w w)
    (hwv : ∀ i, 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w
      (foldedWallFamily (L := L) g hg R i))
    (hR : ∀ i, IsReflectiveRoot L.obj (R i))
    (hneg : ∀ i, L.obj.obj.pairing (R i) (R i) < 0)
    (hcase : ∀ i, g.1 (R i) = R i ∨ L.obj.obj.pairing (R i) (g.1 (R i)) = 0)
    (hsq : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ = -2 ∨
        ((invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ = -4 ∧
          ∀ y : L.obj.obj.carrier,
            (2 : ℤ) ∣ L.obj.obj.pairing (invariantCarrierToAmbient (L := L) g ρ) y))
    (hamb : ∀ ρ ∈ negativeReflectiveRoots L, ∃ c : Fin n → ℤ,
      ρ = ∑ i, c i • R i ∧ ((∀ i, 0 ≤ c i) ∨ ∀ i, c i ≤ 0)) :
    IsChamberWithWalls (invariantFixedLattice (L := L) g) (toRealForm _ w)
      (Set.range (foldedWallFamily (L := L) g hg R)) :=
  isChamberWithWalls_invariant_of_square_criterion (L := L) g hg R w hw
    (foldedWallFamily_mem_negativeReflectiveRoots (L := L) g hg R hR hneg hcase) hwv hsq hamb

end LeanCategories.Lattices.Valued

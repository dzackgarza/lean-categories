/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingChamberOfWallData

/-!
# Positivity against the folded walls, derived (`#116`)

`isChamberWithWalls_invariant_of_wall_data` takes two hypotheses about an interior vector `w`: its
square is positive (`hw`) and it pairs positively with every *folded* wall (`hwv`). The second is
not independent data — it follows from positivity against the *ambient* walls, which is what a
chamber of `L` gives, by the same `ε` mechanism as the fold transfer:

* at a fixed wall, `α^J = α`, so `⟨w, α^J⟩ = ⟨w, α⟩`;
* at a non-fixed wall, `α^J = α + gα` and `w` is fixed, so `⟨w, α^J⟩ = 2⟨w, α⟩`.

Either way the sign is the ambient sign. This is the positivity half of
`foldedVector_pairing_ne_zero_of_mem_interior` (`FoldingInvariantConverse.lean:80`), which gives
only nonvanishing.

* `foldedWallFamily_pairing_pos` — positivity transfers to the folded walls;
* `isChamberWithWalls_invariant_of_wall_data'` — the assembled chamber theorem with `hwv` derived.

The remaining hypotheses of the assembled theorem are then `hw` (an interior vector), the diagram
data (`hR`, `hneg`, `hcase`), and the two external inputs (`hsq`, `hamb`).

## LC-09 record

`rg "pairing_pos|foldedWallFamily_pairing"` gives the nonvanishing statements and the `ε` lemmas,
but no positivity transfer. Nothing ported.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **Positivity against the ambient walls gives positivity against the folded walls.** -/
theorem foldedWallFamily_pairing_pos (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    {n : ℕ} (R : Fin n → L.obj.obj.carrier) (w : involutionFixedSubmodule g)
    (hw : ∀ i, 0 < L.obj.obj.pairing (w : L.obj.obj.carrier) (R i)) :
    ∀ i, 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w
      (foldedWallFamily (L := L) g hg R i) := by
  intro i
  have hcoe : (invariantFixedLattice (L := L) g).obj.obj.pairing w
      (foldedWallFamily (L := L) g hg R i)
      = L.obj.obj.pairing (w : L.obj.obj.carrier) (foldedVector g (R i)) := rfl
  rw [hcoe]
  by_cases hfix : g.1 (R i) = R i
  · rw [foldedVector_of_fixed g hfix]
    exact hw i
  · rw [foldedVector_of_not_fixed g hfix, BilinModuleCat.pairing_add_right]
    have hgy : L.obj.obj.pairing (w : L.obj.obj.carrier) (g.1 (R i))
        = L.obj.obj.pairing (w : L.obj.obj.carrier) (R i) :=
      pairing_isometry_left g hg ((mem_involutionFixedSubmodule_iff g).mp w.2) (R i)
    rw [hgy]
    linarith [hw i]

/-- **The assembled chamber theorem with `hwv` derived.** Same conclusion as
`isChamberWithWalls_invariant_of_wall_data`, with positivity asked only against the *ambient*
walls. -/
theorem isChamberWithWalls_invariant_of_wall_data' (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    {n : ℕ} (R : Fin n → L.obj.obj.carrier) (w : involutionFixedSubmodule g)
    (hw : 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w w)
    (hwamb : ∀ i, 0 < L.obj.obj.pairing (w : L.obj.obj.carrier) (R i))
    (hR : ∀ i, IsReflectiveRoot L.obj (R i))
    (hneg : ∀ i, L.obj.obj.pairing (R i) (R i) < 0)
    (hcase : ∀ i, g.1 (R i) = R i ∨ L.obj.obj.pairing (R i) (g.1 (R i)) = 0)
    (hsq : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ = -2 ∨
        ((invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ = -4 ∧
          ∀ y : L.obj.obj.carrier,
            (2 : ℤ) ∣ L.obj.obj.pairing (invariantToAmbient (L := L) g ρ) y))
    (hamb : ∀ ρ ∈ negativeReflectiveRoots L, ∃ c : Fin n → ℤ,
      ρ = ∑ i, c i • R i ∧ ((∀ i, 0 ≤ c i) ∨ ∀ i, c i ≤ 0)) :
    IsChamberWithWalls (invariantFixedLattice (L := L) g) (toRealForm _ w)
      (Set.range (foldedWallFamily (L := L) g hg R)) :=
  isChamberWithWalls_invariant_of_wall_data (L := L) g hg R w hw
    (foldedWallFamily_pairing_pos (L := L) g hg R w hwamb) hR hneg hcase hsq hamb

end LeanCategories.Lattices.Valued

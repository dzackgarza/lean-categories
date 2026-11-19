/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingChamberPositivity

/-!
# The folded chamber at Definition 3.7's root set (`#116`)

`isChamberWithWalls_invariant_of_wall_data'` concludes at `Set.range (foldedWallFamily g hg R)` —
the fold of the *indexed family*. AEGS Lemma 3.8 (**printed p. 12**) states its conclusion at the
object of Definition 3.7 (**printed p. 12**), the **folded root set** `Λ^{J=1}`: "the walls of `C^J`
are
`α^{J⊥}` for the folded roots in `G(T^dP)^J` ... `C^J` is the fundamental chamber ... and its
Coxeter diagram is the folded diagram `G(T^dP)^J`".

This file restates the theorem at that object. The two sets agree because no fold is dropped:
every fold of the family is a root of `M^σ`
(`foldedWallFamily_mem_negativeReflectiveRoots`), which is what Definition 3.7's filter tests, and
conversely every member of the folded root set is the fold of a family member by construction of
`foldedRootImage`.

* `range_foldedWallFamily_eq_foldedRootSet` — the family's range is Definition 3.7's set;
* `isChamberWithWalls_invariant_of_foldedRootSet` — Lemma 3.8's conclusion at the paper's object.

## LC-09 record

`rg "range_foldedWallFamily|of_foldedRootSet"` gives nothing; `range_foldedDiagramOfRoots_eq`
(`FoldingDiagramOrbits.lean:78`) compares the two spellings only through their coercions into `L`.
Nothing ported.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **The family's range is Definition 3.7's folded root set**, when every fold is a root: the
filter of Definition 3.7 drops nothing. -/
theorem range_foldedWallFamily_eq_foldedRootSet (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    {n : ℕ} (R : Fin n → L.obj.obj.carrier)
    (hR : ∀ i, foldedWallFamily (L := L) g hg R i ∈
      negativeReflectiveRoots (invariantFixedLattice (L := L) g)) :
    Set.range (foldedWallFamily (L := L) g hg R)
      = foldedRootSet (L := L) g (Set.range R) := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    refine (mem_foldedRootSet_iff g (Set.range R) _).mpr ⟨?_, (hR i).2, ?_⟩
    · show ((foldedWallFamily (L := L) g hg R i : involutionFixedSubmodule g) :
        L.obj.obj.carrier) ∈ foldedRootImage g (Set.range R)
      rw [foldedRootImage_range]
      exact ⟨i, rfl⟩
    · intro x
      exact (hR i).1.dvd_two_mul x
  · intro hv
    have himg := ((mem_foldedRootSet_iff g (Set.range R) v).mp hv).1
    rw [foldedRootImage_range] at himg
    obtain ⟨i, hi⟩ := himg
    refine ⟨i, ?_⟩
    exact Subtype.ext hi

/-- **AEGS Lemma 3.8 at Definition 3.7's object**: the folded root set is the wall set of the
chamber, stated with the paper's own `Λ^{J=1}` rather than with the indexing family. -/
theorem isChamberWithWalls_invariant_of_foldedRootSet (g : OrthogonalGroup L.obj) (hg : g * g = 1)
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
            (2 : ℤ) ∣ L.obj.obj.pairing (invariantCarrierToAmbient (L := L) g ρ) y))
    (hamb : ∀ ρ ∈ negativeReflectiveRoots L, ∃ c : Fin n → ℤ,
      ρ = ∑ i, c i • R i ∧ ((∀ i, 0 ≤ c i) ∨ ∀ i, c i ≤ 0)) :
    IsChamberWithWalls (invariantFixedLattice (L := L) g) (toRealForm _ w)
      (foldedRootSet (L := L) g (Set.range R)) := by
  rw [← range_foldedWallFamily_eq_foldedRootSet (L := L) g hg R
    (foldedWallFamily_mem_negativeReflectiveRoots (L := L) g hg R hR hneg hcase)]
  exact isChamberWithWalls_invariant_of_wall_data' (L := L) g hg R w hw hwamb hR hneg hcase hsq hamb

end LeanCategories.Lattices.Valued

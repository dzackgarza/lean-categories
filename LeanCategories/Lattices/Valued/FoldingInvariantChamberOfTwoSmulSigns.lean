/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantChamberOfSigns
public import LeanCategories.Lattices.Valued.NegativeSquareTwoZsmul

/-!
# The folded chamber from a *doubled* one-sign property (`#116`)

`isChamberWithWalls_invariant_of_folded_signs` asks every root `ρ` of `M^σ` to be a same-sign
`ℤ`-combination of the folded walls. Folding does not produce that: it produces, for a root that is
also a root of `L`,

  `2ρ = Σ (cᵢ εᵢ) • Rᵢ^g`,

with the same-sign coefficients `cᵢ εᵢ` (`FoldingSignTransfer.two_smul_eq_sum_smul_foldedVector`).
The factor `2` is not an artefact to be divided away — `cᵢ/2` leaves `ℤ` — but it is *harmless* for
the chamber: at an interior point `z`, `⟨z, 2ρ⟩ = 2⟨z, ρ⟩`, so a nonzero doubled pairing is a
nonzero pairing. This file proves the chamber from the doubled form, so that the transfer composes
with it without leaving `ℤ`.

* `isChamberWithWalls_invariant_of_two_smul_folded_signs` — the chamber, from the doubled one-sign
  property. The nonvanishing `2 • ρ ≠ 0` that the criterion needs is **derived** from `ρ² < 0`
  (`NegativeSquareTwoZsmul.two_zsmul_ne_zero_of_pairing_neg`), so the statement carries no auxiliary
  hypothesis beyond the expansion itself.

Source: AEGS Lemma 3.8 (**printed p. 12**) again; nothing new from the paper, the statement is the
same chamber with the `ℤ`-level form the folding actually yields. The `2` is the `ε` of Lemma 3.4's
proof (**printed p. 12**).

## LC-09 record

`rg "two_smul_eq_sum|isChamberWithWalls_invariant_of"` gives the two #116 modules and no doubled
variant; `pairing_ne_zero_of_signs` (`VinbergE10Chamber.lean:651`) is the undoubled form. Nothing
ported.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **The folded chamber from a doubled one-sign property.**

Same conclusion as `isChamberWithWalls_invariant_of_folded_signs`, with `2 • ρ` in place of `ρ` in
the hypothesis. Since `⟨z, 2ρ⟩ = 2⟨z, ρ⟩` at an interior point, the doubling costs nothing: the
pairing with `z` is nonzero exactly when the doubled one is.

The criterion `pairing_ne_zero_of_signs` also needs `2 • ρ ≠ 0`; that is not a hypothesis but a
consequence of `ρ² < 0` (`two_zsmul_ne_zero_of_pairing_neg`), since a negative-square vector is not
2-torsion. -/
theorem isChamberWithWalls_invariant_of_two_smul_folded_signs (g : OrthogonalGroup L.obj)
    (hg : g * g = 1) [Module.Projective ℤ (involutionFixedSubmodule g)]
    {n : ℕ} (r : Fin n → L.obj.obj.carrier) (w : involutionFixedSubmodule g)
    (hw : 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w w)
    (hroot : ∀ i, foldedWallFamily (L := L) g hg r i ∈
      negativeReflectiveRoots (invariantFixedLattice (L := L) g))
    (hwv : ∀ i, 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w
      (foldedWallFamily (L := L) g hg r i))
    (hsign : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      ∃ b : Fin n → ℤ,
        (2 : ℤ) • ρ = ∑ i, b i • foldedWallFamily (L := L) g hg r i ∧
        ((∀ i, 0 ≤ b i) ∨ ∀ i, b i ≤ 0)) :
    IsChamberWithWalls (invariantFixedLattice (L := L) g) (toRealForm _ w)
      (Set.range (foldedWallFamily (L := L) g hg r)) := by
  refine ⟨?_, ⟨toRealForm _ w, ⟨⟨?_, ?_⟩, ?_⟩⟩, ?_⟩
  · rintro s ⟨i, rfl⟩
    exact hroot i
  · have hQ : 0 < realFormQuadratic (invariantFixedLattice (L := L) g) (toRealForm _ w) := by
      rw [realFormQuadratic_apply]
      rw [invariant_pairing_toRealForm]
      exact_mod_cast hw
    exact hQ
  · have hQ : 0 < realFormQuadratic (invariantFixedLattice (L := L) g) (toRealForm _ w) := by
      rw [realFormQuadratic_apply]
      rw [invariant_pairing_toRealForm]
      exact_mod_cast hw
    rw [associated_self_apply]
    exact hQ
  · intro v hv
    obtain ⟨i, rfl⟩ := hv
    have hpair := invariant_pairing_toRealForm (L := L) g w
      (foldedWallFamily (L := L) g hg r i)
    have hpos : (0 : ℝ) < ((invariantFixedLattice (L := L) g).obj.obj.pairing w
        (foldedWallFamily (L := L) g hg r i) : ℝ) := by
      exact_mod_cast hwv i
    exact hpair ▸ hpos
  · intro z hz
    have hz' : z ∈ positiveCone.upper
        (realFormQuadratic (invariantFixedLattice (L := L) g)) (toRealForm _ w) ∧
        ∀ v ∈ Set.range (foldedWallFamily (L := L) g hg r),
          0 < (realForm (invariantFixedLattice (L := L) g)).obj.pairing z (toRealForm _ v) := hz
    refine (mem_weylRegularLocus_iff (L := invariantFixedLattice (L := L) g)
      (t := toRealForm _ w) (x := z)).mpr ⟨hz'.1, ?_⟩
    intro ρ hρ
    obtain ⟨b, hsum, hsignb⟩ := hsign ρ hρ
    have hne : (2 : ℤ) • ρ ≠ 0 :=
      two_zsmul_ne_zero_of_pairing_neg (L := invariantFixedLattice (L := L) g) hρ.2
    have hne2 : (realForm (invariantFixedLattice (L := L) g)).obj.pairing z
        (toRealForm _ ((2 : ℤ) • ρ)) ≠ 0 :=
      pairing_ne_zero_of_signs (L := invariantFixedLattice (L := L) g)
        (t := toRealForm _ w) (R := foldedWallFamily (L := L) g hg r) hz b hsum hne hsignb
    have hconv : (realForm (invariantFixedLattice (L := L) g)).obj.pairing z
        (toRealForm _ ((2 : ℤ) • ρ)) =
        (2 : ℝ) * (realForm (invariantFixedLattice (L := L) g)).obj.pairing z
          (toRealForm _ ρ) := by
      rw [toRealForm_zsmul, BilinModuleCat.pairing_smul_right, smul_eq_mul]
      norm_num
    rw [hconv] at hne2
    exact right_ne_zero_of_mul hne2

end LeanCategories.Lattices.Valued

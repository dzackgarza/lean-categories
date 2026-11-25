/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantChamber
public import LeanCategories.Lattices.Valued.VinbergE10Chamber

/-!
# The folded chamber from a one-sign property of the folded roots (`#116`)

`FoldingInvariantChamber.isChamberWithWalls_invariant` proves that the folded cone is a chamber with
walls `foldedRootSet g R` from `hcomplete`: every negative reflective root of `M^σ` is a nonzero
integer multiple of a folded wall root. That hypothesis is *false* in the AEGS instance
(`FoldingE10RootNotWall.e10_reflected_root_not_multiple` is the small witness; in the hyperbolic
`T_En` there are infinitely many root lines and at most `|R|` folds), so the theorem is not
instantiable there.

This file proves the same conclusion from a hypothesis that is weaker, and is the one AEGS Lemma
3.8's covering actually supports: every negative reflective root of `M^σ` is a **same-sign**
`ℤ`-combination of the folded wall roots. `hcomplete` is the special case of a one-term
combination, so nothing is lost; and the same-sign form is what the repository already uses for the
`E₁₀(2)` chamber (`VinbergE10Chamber.isChamberWithWalls_of_signs`), which is why the proof below is
a re-use of `pairing_ne_zero_of_signs` rather than a new argument.

* `foldedWallFamily` — the folded roots of a family of wall roots, as vectors of `M^σ`;
* `isChamberWithWalls_invariant_of_folded_signs` — the chamber, from the one-sign property.

No source to cite for the statement itself: it is AEGS Lemma 3.8 (**printed p. 12**) with the
hypothesis that makes it provable, and the one-sign lemma is Bourbaki, Ch. V §1 no. 6 (**printed
pp. 65–66**) in the form the repository's `E₁₀(2)` criterion already carries.

## LC-09 record

`rg "isChamberWithWalls_of_signs|pairing_ne_zero_of_signs"` gives the `E₁₀(2)` criterion
(`VinbergE10Chamber.lean:689,651`) and no folding-level use of it; `rg "folded_signs|hsign"` gives
nothing. Mathlib at the pinned head has `RootPairing.Base` with the one-sign property as a *field*
(`Base.root_mem_or_neg_mem`) under `[Finite ι]`, and no chamber or Tits-cone theory, so nothing is
ported: the pairing argument is the repository's own.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **The folded roots of a family of wall roots**, as vectors of the invariant lattice. The fold is
taken with the membership in `M^σ` carried as data, which is what the involution law is needed
for. -/
noncomputable def foldedWallFamily (g : OrthogonalGroup L.obj) (hg : g * g = 1) {n : ℕ}
    (r : Fin n → L.obj.obj.carrier) : Fin n → involutionFixedSubmodule g :=
  fun i => ⟨foldedVector g (r i), foldedVector_mem_fixed g hg (r i)⟩

/-- **The chamber of `M^σ` with walls the folded roots, from a one-sign property.**

Hypotheses: `r` is a family of wall roots whose folds are roots of `M^σ` (`hroot`), `w` is an
interior vector of the folded cone (`hw`, `hwv`), and every negative reflective root of `M^σ` is a
`ℤ`-combination of the folded wall roots whose coefficients have one sign (`hsign`).

The conclusion is `IsChamberWithWalls` at the folded wall set, i.e. AEGS Lemma 3.8's chamber. The
proof of the third field is `pairing_ne_zero_of_signs` at the invariant lattice: a one-sign
combination of walls pairs to a sum of terms of one sign with an interior point, hence not to
zero. -/
theorem isChamberWithWalls_invariant_of_folded_signs (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    {n : ℕ} (r : Fin n → L.obj.obj.carrier) (w : involutionFixedSubmodule g)
    (hw : 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w w)
    (hroot : ∀ i, foldedWallFamily (L := L) g hg r i ∈
      negativeReflectiveRoots (invariantFixedLattice (L := L) g))
    (hwv : ∀ i, 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w
      (foldedWallFamily (L := L) g hg r i))
    (hsign : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      ∃ b : Fin n → ℤ, ρ = ∑ i, b i • foldedWallFamily (L := L) g hg r i ∧
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
    have hne : ρ ≠ 0 := by
      intro h0
      rw [h0] at hρ
      exact absurd hρ.2 (by simp)
    exact pairing_ne_zero_of_signs (L := invariantFixedLattice (L := L) g)
      (t := toRealForm _ w) (R := foldedWallFamily (L := L) g hg r) hz b hsum hne hsignb

end LeanCategories.Lattices.Valued

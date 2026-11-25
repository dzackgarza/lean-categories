/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingRootReflection

/-!
# An isometry carries a chamber to a chamber (`#116`)

The residual of #116 is `RootsAreFoldsOfWallsCarrier`: every root of `M^σ` is a wall root up to sign
and a **Weyl translate**. The previous file supplied the generators; this one supplies the action:
an
isometry carries a chamber with walls `R` to a chamber with walls `g '' R`.

`isChamberWithWalls_image` — for any isometry `g` of the lattice and any chamber `C(R)`,
`IsChamberWithWalls L t R → IsChamberWithWalls L (g t) (g '' R)`. The three fields come from pairing
invariance (`realFormIsometry_pairing`): the image of an interior point is interior, regularity is
carried across, and the root field from `image_negativeReflectiveRoots`.

This is the one-step form of "the reflection group permutes the chambers" — the statement Bourbaki,
*Lie Groups and Lie Algebras* Ch. V §1 (**no. 4**, chambers and their walls) uses when it says the
group acts on the set of chambers, and Vinberg, Mat. Sb. 87 (1972), **§1**, when `W(Γ)` is built
from the reflections in the roots. Its iterate, together with the orbit statement, is what would
discharge
the residual; the iterate is not taken here.

## LC-09 record

`rg "isChamberWithWalls"` gives the predicate, `e10_isChamberWithWalls`, and
`isChamberWithWalls_of_signs` — no invariance under isometries;
`rg "realFormIsometry_pairing|image_negativeReflectiveRoots"` gives `WeylChambers.lean:648,656`,
the two
tools used here, which had not been put together. Bourbaki's statement is quoted above; the proof is
assembled from those lemmas. Nothing ported.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Ch. V §1 no. 4 (chambers and their walls).
* È. B. Vinberg, Mat. Sb. 87 (1972), §1 (the reflection group of a lattice and its chambers).
* AEGS, arXiv:2312.03638v2, §3.7–3.8, Lemma 3.8 (**printed p. 12**).
-/

@[expose] public section

open QuadraticMap
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **An isometry carries a chamber to the chamber of the image wall set.** -/
theorem isChamberWithWalls_image (g : OrthogonalGroup L.obj)
    (t : (realForm L).obj.carrier) (R : Set L.obj.obj.carrier)
    (hR : IsChamberWithWalls L t R) :
    IsChamberWithWalls L (realFormOrthogonalHom L g t)
      ((g.1 : L.obj.obj.carrier → L.obj.obj.carrier) '' R) where
  roots_mem := by
    rintro _ ⟨r, hr, rfl⟩
    exact (image_negativeReflectiveRoots L g).subset ⟨r, hR.roots_mem hr, rfl⟩
  interior_nonempty := by
    obtain ⟨z, hz⟩ := hR.interior_nonempty
    rw [mem_rootInteriorCone_iff] at hz
    refine ⟨realFormOrthogonalHom L g z, ?_⟩
    rw [mem_rootInteriorCone_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [realFormQuadratic_apply, realFormIsometry_pairing, ← realFormQuadratic_apply]
      exact hz.1.1
    · have h : (realForm L).obj.pairing (realFormOrthogonalHom L g z)
          (realFormOrthogonalHom L g t) = (realForm L).obj.pairing z t :=
        realFormIsometry_pairing L g z t
      rw [← realFormPairing_eq_associated, h, realFormPairing_eq_associated]
      exact hz.1.2
    · rintro _ ⟨r, hr, rfl⟩
      have h : (realForm L).obj.pairing (realFormOrthogonalHom L g z)
          (realFormOrthogonalHom L g (toRealForm L r))
            = (realForm L).obj.pairing z (toRealForm L r) :=
        realFormIsometry_pairing L g z (toRealForm L r)
      rw [← realFormOrthogonalHom_toRealForm L g r, h]
      exact hz.2 r hr
  interior_regular := by
    intro z hz
    -- the inverse image of `z` is an interior point of the original chamber
    have hgg : realFormOrthogonalHom L g (realFormOrthogonalHom L g⁻¹ z) = z := by
      calc realFormOrthogonalHom L g (realFormOrthogonalHom L g⁻¹ z)
          = (realFormOrthogonalHom L g * realFormOrthogonalHom L g⁻¹) z := rfl
        _ = (1 : (realFormQuadratic L).IsometryEquiv (realFormQuadratic L)) z := by
            rw [map_inv, mul_inv_cancel]
        _ = z := rfl
    have hz' : realFormOrthogonalHom L g⁻¹ z ∈ rootInteriorCone L t R := by
      rw [mem_rootInteriorCone_iff] at hz ⊢
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [realFormQuadratic_apply, realFormIsometry_pairing, ← realFormQuadratic_apply]
        exact hz.1.1
      · have h : (realForm L).obj.pairing (realFormOrthogonalHom L g⁻¹ z) t
            = (realForm L).obj.pairing z (realFormOrthogonalHom L g t) := by
          rw [← realFormIsometry_pairing L g (realFormOrthogonalHom L g⁻¹ z) t, hgg]
        rw [← realFormPairing_eq_associated, h, realFormPairing_eq_associated]
        exact hz.1.2
      · intro r hr
        have h : (realForm L).obj.pairing (realFormOrthogonalHom L g⁻¹ z)
            (toRealForm L r)
              = (realForm L).obj.pairing z
                  (realFormOrthogonalHom L g (toRealForm L r)) := by
          rw [← realFormIsometry_pairing L g (realFormOrthogonalHom L g⁻¹ z)
            (toRealForm L r)]
          rw [hgg]
        rw [h, realFormOrthogonalHom_toRealForm]
        exact hz.2 (g.1 r) ⟨r, hr, rfl⟩
    have hzreg := hR.interior_regular hz'
    rw [mem_weylRegularLocus_iff (L := L) (t := t)] at hzreg
    obtain ⟨hzu, _⟩ := (mem_rootInteriorCone_iff (L := L)
      (t := realFormOrthogonalHom L g t)).mp hz
    refine (mem_weylRegularLocus_iff (L := L)
      (t := realFormOrthogonalHom L g t)).mpr ⟨hzu, ?_⟩
    intro ρ hρ
    have hρ'' : ρ ∈ (g.1 : L.obj.obj.carrier → L.obj.obj.carrier) ''
        (negativeReflectiveRoots L) := by
      rw [image_negativeReflectiveRoots L g]
      exact hρ
    rcases hρ'' with ⟨r, hr, rfl⟩
    have hreg := hzreg.2 r hr
    have h : (realForm L).obj.pairing z
        (toRealForm L (g.1 r))
          = (realForm L).obj.pairing (realFormOrthogonalHom L g⁻¹ z) (toRealForm L r) := by
      rw [← realFormOrthogonalHom_toRealForm L g r,
        ← realFormIsometry_pairing L g (realFormOrthogonalHom L g⁻¹ z) (toRealForm L r)]
      rw [hgg]
    rw [h]
    exact hreg

end LeanCategories.Lattices.Valued

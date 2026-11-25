/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingDiagram

/-!
# A diagram involution preserves the chamber cone (`#116`)

The joining theorem (`FoldingInvariantChamber.isChamberWithWalls_invariant_of_chamber`) takes the
hypothesis `hstab` that the involution carries the chamber's interior cone into itself. For the
identity involution that is trivial, and for a *non-trivial* instance it is the one hypothesis that
folding can actually supply — the chamber and the involution are independent data.

This file derives it from what a diagram involution carries: if `g` acts on the simple-root family
`r` through an involution `π` of its index set (`ActsThrough`, `FoldingDiagram.lean`) and fixes a
point `t` of the sheet, then `g` preserves the interior cone of `Set.range r`.

The proof is three lines, one per field of the cone:
* the quadratic form is preserved (`realFormIsometry_pairing`), so `Q (g z) = Q z`;
* the pairing with the sheet point is preserved because `g t = t`;
* the pairing with the wall `r i` becomes the pairing with `r (π i)` — again a wall — because
  `g (r (π i)) = r (π (π i)) = r i`.

So a non-trivial instance of the joining theorem needs only an explicit chamber `IsChamberWithWalls`
whose simple roots are given with a diagram involution, plus the two arithmetic inputs of the module
`FoldingInvariantChamber`; `hstab` is free.

## LC-09 record

Searched the repository for a statement that an isometry preserving a chamber's wall set preserves
its cone: `rg "rootInteriorCone"` over `LeanCategories/Lattices/Valued/WeylChambers.lean` gives
`convex_rootInteriorCone`, `mem_rootInteriorCone_iff` and the chamber theory of `#23`, and
`realFormIsometry_pairing`/`realFormIsometry_image_rootMirror` in the same file give the action of
an isometry on mirrors — but nothing states the invariance of the interior cone under an isometry
that
permutes the wall set. Mathlib at the pinned head has no chamber theory for indefinite lattices. The
Formalization Corpus returns no files for "chamber cone invariant under diagram automorphism".
Nothing ported; the statement is proved from `realFormIsometry_pairing` and `ActsThrough`.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, arXiv:2312.03638v2, §3.7–3.8 (printed
  pp. 11–13): Lemma 3.8's chamber `C` with an involution of the diagram.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Ch. V §1: chambers, walls, and their faces.
-/

@[expose] public section

open QuadraticMap
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **A diagram involution that fixes a point of the sheet preserves the chamber's interior cone.**
This is the `hstab` hypothesis of `isChamberWithWalls_invariant_of_chamber`, derived from the data a
diagram involution actually carries. -/
theorem realFormOrthogonalHom_mem_rootInteriorCone (g : OrthogonalGroup L.obj)
    {ι : Type*} {r : ι → L.obj.obj.carrier} {π : ι → ι} (hπ : ∀ i, π (π i) = i)
    (h : ActsThrough g r π) {t : (realForm L).obj.carrier}
    (ht : realFormOrthogonalHom L g t = t)
    {z : (realForm L).obj.carrier} (hz : z ∈ rootInteriorCone L t (Set.range r)) :
    realFormOrthogonalHom L g z ∈ rootInteriorCone L t (Set.range r) := by
  obtain ⟨⟨hQz, hQt⟩, hzr⟩ := (mem_rootInteriorCone_iff (L := L) (t := t)).mp hz
  refine (mem_rootInteriorCone_iff (L := L) (t := t)).mpr ⟨⟨?_, ?_⟩, ?_⟩
  · -- the quadratic form is preserved
    rw [realFormQuadratic_apply, realFormIsometry_pairing, ← realFormQuadratic_apply]
    exact hQz
  · -- the pairing with the sheet point is preserved, because `g` fixes it
    rw [← realFormPairing_eq_associated] at hQt ⊢
    rw [← ht, realFormIsometry_pairing]
    exact hQt
  · -- the pairing with a wall becomes the pairing with the image wall
    rintro _ ⟨i, rfl⟩
    have hσ : realFormOrthogonalHom L g (toRealForm L (r (π i))) = toRealForm L (r i) := by
      rw [realFormOrthogonalHom_toRealForm, h (π i), hπ i]
    calc (0 : ℝ) < (realForm L).obj.pairing z (toRealForm L (r (π i))) :=
          hzr _ ⟨π i, rfl⟩
      _ = (realForm L).obj.pairing (realFormOrthogonalHom L g z) (toRealForm L (r i)) := by
          rw [← hσ, realFormIsometry_pairing]

/-- The identity involution acts on any root family through the identity permutation, so the lemma
above recovers `hstab` for the identity involution of `FoldingWitness.lean`. -/
theorem actsThrough_one (r : ι → L.obj.obj.carrier) :
    ActsThrough (1 : OrthogonalGroup L.obj) r id := fun _ => rfl

end LeanCategories.Lattices.Valued

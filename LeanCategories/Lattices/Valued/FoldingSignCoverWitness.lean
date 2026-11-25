/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingWitness
public import LeanCategories.Lattices.Valued.FoldingInvariantChamberSignCover

/-!
# A closed witness through the sign covering (`#116`)

The review of `d412b826` observed, correctly, that the sign-covering route's only probe leaves
`hpos` (the signature of the invariant lattice) as an explicit premise, so it is not a *closed*
witness of `IsChamberWithWalls`. This file supplies one: the predicate for the invariant lattice of
the hyperbolic plane at the identity involution, produced through the sign covering, with no
`hcomplete`, no `hpos`, and no hypothesis left over.

It is a second, independent certificate of the same statement as `u_witnessed`
(`FoldingWitness.lean`), which went through `hcomplete`. Together they show that both routes reach
the predicate where a classification exists; neither shows that either hypothesis is derivable from
`IsChamberWithWalls`, and neither is a non-trivial involution.

## LC-09 record

Searched for a closed instance of `isChamberWithWalls_invariant_of_sign_cover`:
`rg "isChamberWithWalls_invariant_of_sign_cover"` gives the theorem and the test in
`FoldingInvariantChamberSignCoverTests.lean`, which leaves `hpos` as a premise; `rg "u_witnessed"`
gives the `hcomplete`-route certificate. Nothing supplies the sign-covering certificate without
`hpos`, which is what this file adds. Mathlib has no chamber theory for indefinite lattices. The
Formalization Corpus returns no files. Nothing ported.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, arXiv:2312.03638v2, §3.7–3.8 (printed
  pp. 11–13).
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

theorem u_invariant_projective :
    Module.Projective ℤ (↥(involutionFixedSubmodule (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))) := by
  have key : Module.Projective ℤ (↥(⊤ : Submodule ℤ (Fin 2 → ℤ))) := by
    have : Module.Projective ℤ (Fin 2 → ℤ) := inferInstance
    exact Module.Projective.of_equiv (Submodule.topEquiv)
  rwa [involutionFixedSubmodule_one]

/-- The fixed sublattice of the identity involution of the hyperbolic plane is projective (it is the
whole lattice), as a global instance so that the invariant lattice object is available without a
hypothesis. -/
instance u_invariantProjectiveInstance :
    Module.Projective ℤ (↥(involutionFixedSubmodule (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))) :=
  u_invariant_projective

/-- **A closed witness through the sign covering**: the invariant lattice of the hyperbolic plane at
the identity involution is a chamber with the folded wall set `{e - f}`, from the interior lattice
vector `e + 2f` and the sign covering `±(e - f)` — with no `hpos` and no `hcomplete`. -/
theorem u_invariant_isChamberWithWalls_signCover :
    IsChamberWithWalls
      (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))
      (toRealForm _ uInteriorFixed)
      (foldedRootSet (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot}) := by
  have hw : 0 < (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing
        uInteriorFixed uInteriorFixed := by
    rw [invariantFixedLattice_pairing]
    change 0 < hyperbolicPlaneFiniteLattice.obj.obj.pairing uInterior uInterior
    rw [uInterior_square]; norm_num
  have hwv : ∀ v ∈ foldedRootSet (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot},
      0 < (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing
          uInteriorFixed v := by
    intro v hv
    rw [u_foldedRootSet_one, Set.mem_singleton_iff] at hv
    subst hv
    rw [invariantFixedLattice_pairing]
    change 0 < hyperbolicPlaneFiniteLattice.obj.obj.pairing uInterior uRoot
    rw [uInterior_pairing_root]; norm_num
  have hcover : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice
      (L := hyperbolicPlaneFiniteLattice) (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      ρ ∈ foldedRootSet (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot} ∨
        -ρ ∈ foldedRootSet (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot} := by
    intro ρ hρ
    rw [u_foldedRootSet_one]
    rcases u_root_classification_fixed ρ hρ with h | h
    · refine Or.inl ?_
      rw [h]; exact Set.mem_singleton uRootFixed
    · refine Or.inr ?_
      rw [h]
      exact Set.mem_singleton_iff.mpr (neg_neg uRootFixed)
  exact isChamberWithWalls_invariant_of_sign_cover
    (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot} uInteriorFixed
    hw hwv hcover

end LeanCategories.Lattices.Valued

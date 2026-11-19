/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantChamberOfSigns
public import LeanCategories.Lattices.Valued.FoldingSignCoverWitness

/-!
# Probe for `isChamberWithWalls_invariant_of_folded_signs`, on the smallest input that decides it

The lemma replaces `hcomplete` by a one-sign property, so what decides it is an instance where the
one-sign property is *not* a single term with a positive coefficient: on the hyperbolic plane at the
identity involution the roots are `±uRoot` (`u_root_classification_fixed`), so both signs occur and
the sign split is exercised. The conclusion must be the chamber `{uRootFixed}` — the chamber
`u_witnessed` obtains by the other route.

The imported `FoldingSignCoverWitness` is what supplies the projectivity instance at the fixed
submodule of the identity involution (`u_invariantProjectiveInstance`), which the lemma's
`[Module.Projective ℤ (involutionFixedSubmodule g)]` needs and which is not synthesizable on its
own — the carrier obstruction recorded in `results/issue-116-report.md`.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The folded wall family of the hyperbolic plane at the identity involution is `{uRootFixed}`. -/
theorem u_foldedWallFamily_one :
    Set.range (foldedWallFamily (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) (one_mul 1)
      (fun _ : Fin 1 => uRoot)) = {uRootFixed} := by
  have hFix : foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRoot = uRoot :=
    foldedVector_of_fixed (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) rfl
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact Set.mem_singleton_iff.mpr (Subtype.ext hFix)
  · intro hv
    refine Set.mem_range.mpr ⟨0, ?_⟩
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    exact Subtype.ext hFix

/-- **The lemma applies at the hyperbolic plane**, with the one-sign hypothesis taken as given.

This is the type-level check: every other hypothesis of
`isChamberWithWalls_invariant_of_folded_signs` is discharged here (the interior vector
`uInteriorFixed` with its two positivity facts, and `hroot` from `u_foldedRootSet_one` through
`foldedRootSet_subset_negativeReflectiveRoots`), and the conclusion is the folded chamber.

What is *not* done here is the discharge of `hsign` itself. At the identity involution the fold is
`uRoot` only propositionally (`foldedVector_of_fixed`), and rewriting a sum of the lattice
carrier by an equality of the fixed submodule's elements runs into the carrier obstruction in
`results/issue-116-report.md` (`↥(involutionFixedSubmodule 1)` against
`↑(invariantFixedLattice 1).obj.obj.carrier`: definitionally equal, not syntactically). That is the
same obstruction that blocks the bridge and the signature, not a defect of this lemma. -/
example
    (hsign : ∀ ρ ∈ negativeReflectiveRoots
        (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      ∃ b : Fin 1 → ℤ,
        ρ = ∑ i, b i • foldedWallFamily (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) (one_mul 1)
          (fun _ : Fin 1 => uRoot) i ∧
        ((∀ i, 0 ≤ b i) ∨ ∀ i, b i ≤ 0)) :
    IsChamberWithWalls
      (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))
      (toRealForm _ uInteriorFixed)
      (Set.range (foldedWallFamily (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) (one_mul 1)
        (fun _ : Fin 1 => uRoot))) := by
  refine isChamberWithWalls_invariant_of_folded_signs
    (L := hyperbolicPlaneFiniteLattice)
    (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) (one_mul 1)
    (r := fun _ : Fin 1 => uRoot) (w := uInteriorFixed) ?_ ?_ ?_ hsign
  · rw [invariantFixedLattice_pairing]
    change 0 < hyperbolicPlaneFiniteLattice.obj.obj.pairing uInterior uInterior
    rw [uInterior_square]; norm_num
  · intro i
    refine foldedRootSet_subset_negativeReflectiveRoots (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot} ?_
    rw [u_foldedRootSet_one]
    refine Set.mem_singleton_iff.mpr (Subtype.ext ?_)
    exact foldedVector_of_fixed (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) rfl
  · intro i
    rw [invariantFixedLattice_pairing]
    have hFi : ((foldedWallFamily (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) (one_mul 1)
        (fun _ : Fin 1 => uRoot) i : involutionFixedSubmodule
          (L := hyperbolicPlaneFiniteLattice)
            (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) :
        hyperbolicPlaneFiniteLattice.obj.obj.carrier) = uRoot := by
      change foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRoot = uRoot
      exact foldedVector_of_fixed (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) rfl
    rw [hFi]
    change 0 < hyperbolicPlaneFiniteLattice.obj.obj.pairing uInterior uRoot
    rw [uInterior_pairing_root]; norm_num

end LeanCategories.Lattices.Valued

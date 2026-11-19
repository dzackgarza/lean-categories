/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantChamberOfTwoSmulSigns
public import LeanCategories.Lattices.Valued.FoldingSignCoverWitness

/-!
# Probe for `isChamberWithWalls_invariant_of_two_smul_folded_signs`

The theorem is the chamber theorem with `2 • ρ` in place of `ρ` in its hypothesis, so what decides
it is that the doubling is *not* a weakening of the conclusion: applied at the hyperbolic plane with
identity involution, with the doubled one-sign hypothesis taken as given, it must produce the same
chamber `{uRootFixed}` that `isChamberWithWalls_invariant_of_folded_signs` produces from the
undoubled hypothesis.

The point of the doubled form is composition:
`FoldingSignTransfer.two_smul_eq_sum_smul_foldedVector` produces exactly
`2 • ρ = Σ (cᵢ εᵢ) • Rᵢ^g`, so the two statements fit together over `ℤ` without a division that
would leave the lattice.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The doubled form applies at the plane and yields the folded chamber. -/
example
    (hsign : ∀ ρ ∈ negativeReflectiveRoots
        (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      ∃ b : Fin 1 → ℤ,
        (2 : ℤ) • ρ = ∑ i, b i • foldedWallFamily (L := hyperbolicPlaneFiniteLattice)
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
  refine isChamberWithWalls_invariant_of_two_smul_folded_signs
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

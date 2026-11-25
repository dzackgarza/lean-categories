/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingChamberOfSquareCriterion
public import LeanCategories.Lattices.Valued.FoldingInvariantChamberOfTwoSmulSignsTests

/-!
# Probe for `isChamberWithWalls_invariant_of_square_criterion`

The theorem is the composition with its class restriction replaced by the square criterion, so what
decides it is that the replacement really is a *replacement*: applied at the hyperbolic plane's
identity involution, with the square criterion and the ambient expansion taken as hypotheses, it
must produce the folded chamber — the same conclusion as the `hsub` version, from the weaker
hypothesis.

Neither hypothesis is discharged here: the square criterion is a statement about the plane's root
set, and the ambient expansion is Vinberg's theorem. What the probe checks is the composition of the
two #116 criteria into the chamber theorem's assumption.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The chamber theorem with the square criterion at the plane's identity involution. -/
example
    (hsq : ∀ ρ ∈ negativeReflectiveRoots
        (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing ρ ρ = -2 ∨
        ((invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
            (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing ρ ρ = -4 ∧
          ∀ y : hyperbolicPlaneFiniteLattice.obj.obj.carrier,
            (2 : ℤ) ∣ hyperbolicPlaneFiniteLattice.obj.obj.pairing
              (invariantCarrierToAmbient (L := hyperbolicPlaneFiniteLattice)
                (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) ρ) y))
    (hamb : ∀ ρ ∈ negativeReflectiveRoots hyperbolicPlaneFiniteLattice, ∃ c : Fin 1 → ℤ,
      ρ = ∑ i, c i • (fun _ : Fin 1 => uRoot) i ∧
        ((∀ i, 0 ≤ c i) ∨ ∀ i, c i ≤ 0)) :
    IsChamberWithWalls
      (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))
      (toRealForm _ uInteriorFixed)
      (Set.range (foldedWallFamily (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) (one_mul 1)
        (fun _ : Fin 1 => uRoot))) := by
  refine isChamberWithWalls_invariant_of_square_criterion
    (L := hyperbolicPlaneFiniteLattice)
    (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) (one_mul 1)
    (R := fun _ : Fin 1 => uRoot) (w := uInteriorFixed) ?_ ?_ ?_ hsq hamb
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

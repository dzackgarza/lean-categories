/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantChamberOfAmbientSigns
public import LeanCategories.Lattices.Valued.FoldingInvariantChamberOfTwoSmulSignsTests

/-!
# Probe for `isChamberWithWalls_invariant_of_ambient_signs`

The theorem composes the transfer with the doubled chamber criterion through the carrier bridge, so
what decides it is that the composition produces the *same* chamber the direct route produces: at
the plane's identity involution, with the class restriction and the ambient expansion taken as
hypotheses, it must yield the folded chamber — `Set.range (foldedWallFamily …)`, which
`u_foldedWallFamily_one` identifies with `{uRootFixed}`, the chamber `u_witnessed` obtains.

What the probe does not decide is the ambient expansion itself: that is Vinberg's one-sign theorem
for the wall family of `L`, which the development does not have (no chambers, no Tits cone in
Mathlib), so it stays a hypothesis here as in the theorem.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The composition yields the folded chamber on the plane at the identity involution. -/
example
    (hsub : ∀ ρ ∈ negativeReflectiveRoots
        (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      invariantCarrierToAmbient (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) ρ ∈
        negativeReflectiveRoots hyperbolicPlaneFiniteLattice)
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
  have hmain := isChamberWithWalls_invariant_of_ambient_signs
    (L := hyperbolicPlaneFiniteLattice)
    (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) (one_mul 1)
    (R := fun _ : Fin 1 => uRoot) (w := uInteriorFixed)
    (hw := by
      rw [invariantFixedLattice_pairing]
      change 0 < hyperbolicPlaneFiniteLattice.obj.obj.pairing uInterior uInterior
      rw [uInterior_square]; norm_num)
    (hroot := by
      intro i
      refine foldedRootSet_subset_negativeReflectiveRoots (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot} ?_
      rw [u_foldedRootSet_one]
      refine Set.mem_singleton_iff.mpr (Subtype.ext ?_)
      exact foldedVector_of_fixed (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) rfl)
    (hwv := by
      intro i
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
      rw [uInterior_pairing_root]; norm_num)
    hsub hamb
  exact hmain

end LeanCategories.Lattices.Valued

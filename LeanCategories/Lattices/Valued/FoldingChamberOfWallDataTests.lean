/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingChamberOfWallData
public import LeanCategories.Lattices.Valued.FoldingSignCoverWitness

/-!
# Probe for the assembled chamber theorem

The theorem is an assembly: it composes `foldedWallFamily_mem_negativeReflectiveRoots` with
`isChamberWithWalls_invariant_of_square_criterion`. What decides the assembly is that the hypothesis
lists really line up — the per-wall data (`hR`, `hneg`, `hcase`) supplies exactly what the
criterion's `hroot` needs, with nothing left over — so the probe instantiates it at the hyperbolic
plane with every hypothesis named explicitly and checks that the conclusion is the folded chamber.

None of the hypotheses is discharged: three are diagram-level data and two are the external inputs
(Namikawa, Vinberg). The point is the shape of the statement.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The assembled chamber theorem at the plane's identity involution. -/
example
    (hw : 0 < (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing
        uInteriorFixed uInteriorFixed)
    (hwv : ∀ i, 0 < (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing uInteriorFixed
        (foldedWallFamily (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) (one_mul 1)
          (fun _ : Fin 1 => uRoot) i))
    (hR : ∀ _ : Fin 1, IsReflectiveRoot hyperbolicPlaneFiniteLattice.obj uRoot)
    (hneg : ∀ _ : Fin 1,
      hyperbolicPlaneFiniteLattice.obj.obj.pairing uRoot uRoot < 0)
    (hcase : ∀ _ : Fin 1,
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj).1 uRoot = uRoot ∨
        hyperbolicPlaneFiniteLattice.obj.obj.pairing uRoot
          ((1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj).1 uRoot) = 0)
    (hsq : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice
        (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing ρ ρ = -2 ∨
        ((invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
            (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing ρ ρ = -4 ∧
          ∀ y : hyperbolicPlaneFiniteLattice.obj.obj.carrier,
            (2 : ℤ) ∣ hyperbolicPlaneFiniteLattice.obj.obj.pairing
              (invariantToAmbient (L := hyperbolicPlaneFiniteLattice)
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
        (fun _ : Fin 1 => uRoot))) :=
  isChamberWithWalls_invariant_of_wall_data (L := hyperbolicPlaneFiniteLattice)
    (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) (one_mul 1)
    (R := fun _ : Fin 1 => uRoot) (w := uInteriorFixed) hw hwv hR hneg hcase hsq hamb

end LeanCategories.Lattices.Valued

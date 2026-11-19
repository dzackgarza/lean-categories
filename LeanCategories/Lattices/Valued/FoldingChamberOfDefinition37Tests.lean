/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingChamberOfDefinition37
public import LeanCategories.Lattices.Valued.FoldingInvariantChamberOfTwoSmulSignsTests

/-!
# Probe for the Definition 3.7 restatement

The equality says the family's range is the folded root set when no fold is dropped. At the
hyperbolic plane's identity involution both sides were computed earlier in the #116 chain: the
family's range is `{uRootFixed}` (`u_foldedWallFamily_one`) and so is Definition 3.7's set
(`u_foldedRootSet_one`), so the probe derives the equality rather than assuming it.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The family's range is Definition 3.7's folded root set, at the plane — both computed. -/
example : Set.range (foldedWallFamily (L := hyperbolicPlaneFiniteLattice)
    (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) (one_mul 1)
    (fun _ : Fin 1 => uRoot))
      = foldedRootSet (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)
        (Set.range (fun _ : Fin 1 => uRoot)) := by
  refine range_foldedWallFamily_eq_foldedRootSet (L := hyperbolicPlaneFiniteLattice)
    (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) (one_mul 1)
    (fun _ : Fin 1 => uRoot) ?_
  intro i
  refine foldedRootSet_subset_negativeReflectiveRoots (L := hyperbolicPlaneFiniteLattice)
    (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot} ?_
  rw [u_foldedRootSet_one]
  refine Set.mem_singleton_iff.mpr ?_
  exact Subtype.ext (foldedVector_of_fixed
    (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) rfl)

end LeanCategories.Lattices.Valued

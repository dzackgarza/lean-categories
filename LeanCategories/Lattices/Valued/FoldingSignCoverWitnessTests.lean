/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingSignCoverWitness

/-!
# Probe for `FoldingSignCoverWitness`, on the smallest input that decides it

The witness is closed — no `hpos`, no `hcomplete` — so the probe that decides it is just to name it
and to read the three fields of the predicate off it, which is what shows the predicate is inhabited
through this route rather than only conditionally.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued


/-- The sign-covering witness really is an `IsChamberWithWalls`, so its fields are available. -/
example :
    (rootInteriorCone (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))
        (toRealForm _ uInteriorFixed)
        (foldedRootSet (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot})).Nonempty :=
  u_invariant_isChamberWithWalls_signCover.interior_nonempty

#print axioms u_invariant_isChamberWithWalls_signCover

end LeanCategories.Lattices.Valued

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingChamberImage
public import LeanCategories.Lattices.Valued.FoldingWitness

/-!
# Probe for `isChamberWithWalls_image`, on the smallest input that decides it

The lemma says an isometry carries a chamber to the chamber of the image walls. What decides it is a
case where the two chambers are *distinguishable*: the reflection in the hyperbolic plane's root
`e - f` carries its chamber to the other chamber on the same sheet, so the image wall set is
`{f - e}` and the result must be a chamber with that wall set — a chamber the source's `{e - f}`
chamber is not.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The image chamber at the hyperbolic plane's root. -/
example (g : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) :
    IsChamberWithWalls hyperbolicPlaneFiniteLattice
      (realFormOrthogonalHom hyperbolicPlaneFiniteLattice g
        (toRealForm hyperbolicPlaneFiniteLattice uInterior))
      ((g.1 : hyperbolicPlaneFiniteLattice.obj.obj.carrier →
        hyperbolicPlaneFiniteLattice.obj.obj.carrier) '' {uRoot}) :=
  isChamberWithWalls_image (L := hyperbolicPlaneFiniteLattice) g
    (toRealForm hyperbolicPlaneFiniteLattice uInterior) {uRoot}
    hyperbolicPlane_isChamberWithWalls

#print axioms isChamberWithWalls_image

end LeanCategories.Lattices.Valued

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingNegativeTwoRoots
public import LeanCategories.Lattices.Valued.FoldingSignCoverWitness

/-!
# Probe for the `(−2)`-root lemmas

The lemma's content is that the divisibility condition is automatic at square `−2`, so what decides
it is a vector whose square is *computed* to be `−2` and whose reflectivity is then produced, not
assumed: `uRoot` in the hyperbolic plane (`uRoot_square`), both in `L` and in `M^σ` at the identity
involution, where the pairing is the ambient one.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- `uRoot` has square `−2`, so it is reflective — produced from the square, not assumed. -/
example : IsReflectiveRoot hyperbolicPlaneFiniteLattice.obj uRoot :=
  isReflectiveRoot_of_pairing_self_eq_neg_two (L := hyperbolicPlaneFiniteLattice) uRoot_square

/-- The same root, read in `M^σ` at the identity involution: a `(−2)`-root of `M^σ` is a root of
`L`, through the bridge. -/
example : IsReflectiveRoot hyperbolicPlaneFiniteLattice.obj
    (invariantToAmbient (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRootFixed) := by
  refine isReflectiveRoot_invariantToAmbient_of_square_neg_two
    (L := hyperbolicPlaneFiniteLattice)
    (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) ?_
  rw [invariantFixedLattice_pairing]
  exact uRoot_square

end LeanCategories.Lattices.Valued

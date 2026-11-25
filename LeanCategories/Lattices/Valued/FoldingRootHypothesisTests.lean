/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingRootHypothesis
public import LeanCategories.Lattices.Valued.FoldingSignCoverWitness

/-!
# Probe for the derived `hroot`

The theorem turns three per-wall conditions into `hroot`. At the hyperbolic plane's identity
involution every wall is fixed, so the probe exercises the *fixed* branch: `uRoot` is reflective and
of square `−2`, and the fold is `uRoot` itself, so the conclusion is the concrete membership of
`uRoot` in the negative reflective roots of `M^σ` — computed, not assumed.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The derived `hroot` at the plane's identity involution: `uRoot` folds to itself and is a
root. -/
example : ∀ i, foldedWallFamily (L := hyperbolicPlaneFiniteLattice)
    (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) (one_mul 1)
    (fun _ : Fin 1 => uRoot) i ∈
      negativeReflectiveRoots (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) := by
  refine foldedWallFamily_mem_negativeReflectiveRoots (L := hyperbolicPlaneFiniteLattice)
    (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) (one_mul 1)
    (R := fun _ : Fin 1 => uRoot) ?_ ?_ ?_
  · intro i
    exact isReflectiveRoot_of_pairing_self_eq_neg_two (L := hyperbolicPlaneFiniteLattice)
      uRoot_square
  · intro i
    rw [uRoot_square]
    norm_num
  · intro i
    exact Or.inl rfl

end LeanCategories.Lattices.Valued

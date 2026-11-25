/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingRootsAreFoldsCarrier
public import LeanCategories.Lattices.Valued.FoldingSignCoverWitness

/-!
# Probe for the carrier form of the converse predicate

Two things decide it: that the carrier form is *statable* where the subtype form's coercion fails,
and
that it implies `hcomplete` at the carrier — the shape `isChamberWithWalls_invariant_of_sign_cover`
consumes. Both are read at the hyperbolic plane's identity involution.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The carrier-level covering, instantiated at the hyperbolic plane: it is exactly the statement
the
chamber predicate needs, with no conversion. -/
example :
    ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice
        (L := hyperbolicPlaneFiniteLattice) (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      ρ ∈ foldedRootSet (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot} ∨
        -ρ ∈ foldedRootSet (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot} := by
  refine signCover_of_rootsAreFoldsOfWallsCarrier (L := hyperbolicPlaneFiniteLattice)
    (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) (one_mul 1) {uRoot} ?_
  intro ρ hρ
  rcases u_root_classification_fixed ρ hρ with h | h
  · refine ⟨uRoot, Set.mem_singleton uRoot, Or.inl ?_⟩
    rw [h]
    exact Subtype.ext (by
      change (uRootFixed : hyperbolicPlaneFiniteLattice.obj.obj.carrier)
        = foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRoot
      have hfix := foldedVector_of_fixed (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)
        (x := uRoot) rfl
      rw [hfix]
      rfl)
  · refine ⟨uRoot, Set.mem_singleton uRoot, Or.inr ?_⟩
    rw [h]
    exact Subtype.ext (by
      change (-uRootFixed : hyperbolicPlaneFiniteLattice.obj.obj.carrier)
        = -foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRoot
      have hfix := foldedVector_of_fixed (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)
        (x := uRoot) rfl
      rw [hfix]
      rfl)

#print axioms hcomplete_of_rootsAreFoldsOfWallsCarrier

end LeanCategories.Lattices.Valued

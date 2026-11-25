/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingRootsAreFolds
public import LeanCategories.Lattices.Valued.FoldingSignCoverWitness

/-!
# Probe for `RootsAreFoldsOfWalls`, on the smallest input that decides it

The predicate is the hypothesis the general chamber theorem reduces to, so what decides it is an
instance where it *holds* and its consequences fire: the hyperbolic plane at the identity
involution,
where the folded root set is `{e - f}` and the roots are `±(e - f)` (`u_root_classification_fixed`).
The probe checks that the predicate is inhabited there and that `hcomplete` follows from it by the
new
route, not by the old classification.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- At the identity involution of the hyperbolic plane every root is a folded wall root. -/
theorem u_rootsAreFoldsOfWalls :
    RootsAreFoldsOfWalls (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot} := by
  intro v hv
  have hfix : foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRoot
      = uRoot := foldedVector_of_fixed _ rfl
  rcases u_root_classification_fixed v hv with h | h
  · refine ⟨uRoot, Set.mem_singleton uRoot, Or.inl ?_⟩
    rw [hfix]
    exact congrArg Subtype.val h
  · refine ⟨uRoot, Set.mem_singleton uRoot, Or.inr ?_⟩
    rw [hfix]
    rw [show ((v : hyperbolicPlaneFiniteLattice.obj.obj.carrier))
        = -((uRootFixed : hyperbolicPlaneFiniteLattice.obj.obj.carrier)) from by
      rw [h]; rfl]
    rfl

/-- **`hcomplete` follows from the new predicate** — the point of the reduction. -/
example :
    ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice
        (L := hyperbolicPlaneFiniteLattice) (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      ∃ v ∈ foldedRootSet (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot},
        ∃ k : ℤ, k ≠ 0 ∧ ρ = k • v :=
  hcomplete_of_rootsAreFoldsOfWalls (L := hyperbolicPlaneFiniteLattice)
    (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot} u_rootsAreFoldsOfWalls

#print axioms hcomplete_of_rootsAreFoldsOfWalls

end LeanCategories.Lattices.Valued

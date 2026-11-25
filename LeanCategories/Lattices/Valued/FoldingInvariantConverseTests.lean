/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantConverse
public import LeanCategories.Lattices.Valued.FoldingWitness

/-!
# Probes for `FoldingInvariantConverse`, on the smallest input that decides it

The module replaces `hcomplete` (every root of `M^σ` is an integer multiple of a *wall* root) by the
two statements that actually compose to it: Lemma 3.4's converse (every root of `M^σ` is the fold of
an ambient root) and the covering of the folds by the wall set. Two things decide that:

* the wall covering holds where the classification says it does — on `U` at the identity involution,
  where the folded root set is `{e - f}` (`u_foldedRootSet_one`) and the roots are `±(e - f)`
  (`u_root_classification_fixed`);
* a wall root's fold is not orthogonal to an interior point of the chamber
  (`foldedVector_pairing_ne_zero_of_mem_interior`), which is the content `hcomplete` was standing in
  for.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- Every root of the invariant lattice of the identity involution of `U` is a folded wall root. -/
example [Module.Projective ℤ (involutionFixedSubmodule (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))]
    (ρ : involutionFixedSubmodule (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))
    (hρ : ρ ∈ negativeReflectiveRoots (invariantFixedLattice
      (L := hyperbolicPlaneFiniteLattice) (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))) :
    ρ ∈ foldedRootSet (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot} ∨
      -ρ ∈ foldedRootSet (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot} := by
  rw [u_foldedRootSet_one]
  rcases u_root_classification_fixed ρ hρ with h | h
  · refine Or.inl ?_
    rw [h]
    exact Set.mem_singleton uRootFixed
  · refine Or.inr ?_
    rw [h]
    have hneg : -(-uRootFixed) = uRootFixed := neg_neg _
    rw [hneg]
    exact Set.mem_singleton uRootFixed

#print axioms foldedVector_pairing_ne_zero_of_mem_interior
#print axioms hcomplete_of_sign_cover

end LeanCategories.Lattices.Valued

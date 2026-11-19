/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingFoldOfRoot
public import LeanCategories.Lattices.Valued.FoldingSignCoverWitness

/-!
# Probe for the type (3) fold lemma

The lemma's content is bilinear: the folded square is `2α²` when `α ⊥ gα`, and the pairing with a
fixed vector doubles. Both halves are already in the repository as identities
(`pairing_folded_self_of_not_fixed`, `pairing_fixed_folded_of_not_fixed`); what this probe decides
is that they compose into reflectivity at `M^σ`'s carrier — the divisibility `2α² ∣ 4⟨α, x⟩` coming
from `α² ∣ 2⟨α, x⟩`.

No concrete instance is exhibited: a non-trivial involution of the hyperbolic plane with a
projective fixed submodule is `FoldingRootReflection.rootReflection`, which needs the invariant
lattice, and the repository has no non-trivial chamber-preserving involution with a tabulated
diagram (that is the rigidity result of `FoldingE10Rigidity`). So the hypotheses stay hypotheses, at
the plane, with an arbitrary involution — which does check that the statement is the one the
development can use.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The type (3) fold lemma, at the hyperbolic plane with an arbitrary involution. -/
example (g : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) (hg : g * g = 1)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    (α : hyperbolicPlaneFiniteLattice.obj.obj.carrier)
    (hα : IsReflectiveRoot hyperbolicPlaneFiniteLattice.obj α)
    (horth : hyperbolicPlaneFiniteLattice.obj.obj.pairing α (g.1 α) = 0)
    (hne : g.1 α ≠ α) :
    IsReflectiveRoot
      (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice) g).obj
      (⟨foldedVector g α, foldedVector_mem_fixed g hg α⟩ : involutionFixedSubmodule g) :=
  isReflectiveRoot_foldedVector_of_orthogonal (L := hyperbolicPlaneFiniteLattice) g hg hα horth hne

end LeanCategories.Lattices.Valued

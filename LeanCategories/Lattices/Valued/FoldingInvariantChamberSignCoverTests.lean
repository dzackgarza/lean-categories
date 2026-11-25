/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantChamberSignCover
public import LeanCategories.Lattices.Valued.FoldingWitness

/-!
# Probes for `FoldingInvariantChamberSignCover`, on the smallest input that decides it

The module closes the chamber-theorem chain for the *true* arithmetic input (the sign covering)
instead of `hcomplete`. It is decided on the hyperbolic plane at the identity involution, where
`u_root_classification_fixed` supplies the covering and `u_foldedRootSet_one` says the folded root
set
is `{e - f}`: the chamber of the invariant lattice at `e + 2f` is the folded cone.

The signature hypothesis `hpos` is left as an input of the probe: that the invariant lattice of the
identity involution has signature `(1, 1)` follows from `⊤ ≅ U`, and transporting the signature
through that isometry is not yet built (it is the same carrier-level transport that blocks the
bridge's injectivity).
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- **The chamber of the invariant lattice is the folded cone**, from the sign covering alone. -/
example [Module.Projective ℤ (involutionFixedSubmodule (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))]
    (hpos : (integralSignature (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))).1 = 1) :
    chamberOf (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))
        (toRealForm _ uInteriorFixed)
        (toRealForm _ uInteriorFixed)
      = rootInteriorCone (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))
          (toRealForm _ uInteriorFixed)
          (foldedRootSet (L := hyperbolicPlaneFiniteLattice)
            (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot}) := by
  have hw : 0 < (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing
        uInteriorFixed uInteriorFixed := by
    rw [invariantFixedLattice_pairing]
    change 0 < hyperbolicPlaneFiniteLattice.obj.obj.pairing uInterior uInterior
    rw [uInterior_square]; norm_num
  have hwv : ∀ v ∈ foldedRootSet (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot},
      0 < (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing
          uInteriorFixed v := by
    intro v hv
    rw [u_foldedRootSet_one, Set.mem_singleton_iff] at hv
    subst hv
    rw [invariantFixedLattice_pairing]
    change 0 < hyperbolicPlaneFiniteLattice.obj.obj.pairing uInterior uRoot
    rw [uInterior_pairing_root]; norm_num
  have hcover : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice
      (L := hyperbolicPlaneFiniteLattice) (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      ρ ∈ foldedRootSet (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot} ∨
        -ρ ∈ foldedRootSet (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot} := by
    intro ρ hρ
    rw [u_foldedRootSet_one]
    rcases u_root_classification_fixed ρ hρ with h | h
    · refine Or.inl ?_
      rw [h]; exact Set.mem_singleton uRootFixed
    · refine Or.inr ?_
      rw [h]
      exact Set.mem_singleton_iff.mpr (neg_neg uRootFixed)
  exact chamberOf_invariant_folded_of_sign_cover (L := hyperbolicPlaneFiniteLattice)
    (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot} uInteriorFixed
    hw hwv hcover hpos

#print axioms chamberOf_invariant_folded_of_sign_cover

end LeanCategories.Lattices.Valued

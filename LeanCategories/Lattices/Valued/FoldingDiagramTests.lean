/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingDiagram

/-!
# Probes for `#116` stage 2, on the smallest inputs that decide them

`FoldingDiagram.lean` folds a chamber along a *diagram* involution. The obligations are decided
here on the smallest inputs that carry the answer:

* the worked folded diagram of AEGS Lemma 3.9 (the `E₈` block of `T_dP` under `I = -I_En`): the
  eight folded vectors are fixed by the involution and have square `-4`, their pairwise pairings
  are twice the `E₈` Gram entries, and the folded weight of an `E₈` edge is `1/4`;
* the two `E₈` faces of a diagram involution: the fold is constant on orbits
  (`actsThrough_foldedVector_eq`) and the folded diagram is invariant (`foldedCoxeterDiagram_edges
  _actsThrough`), checked on the identity diagram involution of `E₁₀(2)`'s chamber, where the
  claims are *not* vacuous as statements about the fold: `foldedVector 1 x = x`;
* the axiom footprint of the new theorems.
-/

@[expose] public section

open QuadraticMap
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-! ## The worked folded diagram: the `E₈` block of `T_dP` -/

/-- Definition 3.3 on a real root: a first-`E₈` simple root is not fixed, so its folded vector is
`α + I α` — here `eᵢ - eᵢ'`, the anti-diagonal vector of the two `E₈` blocks. -/
example : foldedVector tdpIsometry (tdpE8Root 0) = tdpE8Root 0 + tdpE8RootImage 0 :=
  foldedVector_of_not_fixed tdpIsometry (tdpE8Root_not_fixed 0)

/-- The fold is a vector of the invariant sublattice `T_En = T_dP^{I=1}`. -/
example : foldedVector tdpIsometry (tdpE8Root 0) ∈
    involutionFixedSubmodule (L := tdpFiniteLattice) tdpIsometry :=
  tdpFoldedE8Root_mem_fixed 0

/-- The folded vector has square `-4`: it is a root of `T_En` and not of `T_dP`. -/
example :
    tdpFiniteLattice.obj.obj.pairing (foldedVector tdpIsometry (tdpE8Root 0))
      (foldedVector tdpIsometry (tdpE8Root 0)) = -4 :=
  tdpFoldedE8Root_square 0

/-- Its pairing with the fold of a second `E₈` simple root is twice the `E₈` Gram entry: `0` for
`e₀` and `e₁`, `2` for `e₀` and the adjacent `e₂` (the `E₈` Gram entry there is `1`). -/
example :
    tdpFiniteLattice.obj.obj.pairing (foldedVector tdpIsometry (tdpE8Root 0))
      (foldedVector tdpIsometry (tdpE8Root 2)) = 2 := by
  rw [tdpFoldedE8Root_pairing, e8GramMatrix_eq]
  norm_num

/-- **The folded weight of an `E₈` edge is `1/4`**: the published folded diagram of the `E₈` block
is `E₈(2)`, a diagram of eight vertices of square `-4` with every edge weight `1/4`. -/
example :
    coxeterDiagramOfRootsEdges tdpFiniteLattice
      (foldedRootFamily tdpIsometry tdpE8Root) 2 3 = 1 / 4 :=
  tdpFoldedE8Diagram_edges_adjacent

/-- Two vertices of the folded diagram that were orthogonal in `E₈` stay orthogonal. -/
example :
    coxeterDiagramOfRootsEdges tdpFiniteLattice
      (foldedRootFamily tdpIsometry tdpE8Root) 0 1 = 0 := by
  rw [tdpFoldedE8Diagram_edges, e8GramMatrix_eq]
  norm_num

/-! ## The two faces of a diagram involution -/

/-- On the identity diagram involution of `E₁₀(2)`'s chamber, the fold is the identity on the
root family — so the orbit form of the folded set is the root set itself. -/
example (i : Fin 10) :
    foldedVector (1 : OrthogonalGroup e10FiniteLattice.obj) (e10SimpleRoot i)
      = e10SimpleRoot i := by
  apply foldedVector_of_fixed
  rfl

/-- A diagram involution acts through the identity permutation on any root family it fixes, and
`actsThrough_foldedVector_eq` is then the statement that the fold is constant on the (singleton)
orbits. -/
example : ActsThrough (1 : OrthogonalGroup e10FiniteLattice.obj) e10SimpleRoot id := by
  intro i
  rfl

/-! ## Axiom footprint -/

#print axioms chamberOf_folded_trace_walls
#print axioms rootMirrorCone_folded_iff
#print axioms actsThrough_involutive
#print axioms tdpFoldedE8Diagram_edges

end LeanCategories.Lattices.Valued

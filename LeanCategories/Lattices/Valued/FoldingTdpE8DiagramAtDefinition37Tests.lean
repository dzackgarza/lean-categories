/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingTdpE8DiagramAtDefinition37

/-!
# Probe: the worked diagram is Definition 3.7's diagram

Item 5's declaration `tdpFoldedE8Diagram` is family-indexed; Definition 3.7's object is indexed
by the surviving folds. The probes decide that the edge weights agree at corresponding vertices, and
evaluate one of them — the adjacent pair `(2,3)` — to `1/4`, matching
`tdpFoldedE8Diagram_adjacent`, so the identification is not vacuous.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The identification of edge weights at corresponding vertices. -/
example
    (hroot : ∀ i : Fin 8,
      (⟨foldedVector tdpIsometry (tdpE8Root i),
        foldedVector_mem_fixed tdpIsometry tdpIsometry_mul_self (tdpE8Root i)⟩ :
          involutionFixedSubmodule tdpIsometry) ∈
        foldedRootSet tdpIsometry (Set.range (fun i : Fin 8 => tdpE8Root i)))
    (i j : Fin 8) :
    tdpFoldedE8Diagram.edges i j =
      (foldedDiagramOfRoots tdpIsometry (Set.range (fun i : Fin 8 => tdpE8Root i))).edges
        (tdpE8Fold hroot i) (tdpE8Fold hroot j) :=
  tdpFoldedE8Diagram_edges_eq_foldedDiagramOfRoots hroot i j

/-- And the published adjacent weight survives the change of indexing. -/
example
    (hroot : ∀ i : Fin 8,
      (⟨foldedVector tdpIsometry (tdpE8Root i),
        foldedVector_mem_fixed tdpIsometry tdpIsometry_mul_self (tdpE8Root i)⟩ :
          involutionFixedSubmodule tdpIsometry) ∈
        foldedRootSet tdpIsometry (Set.range (fun i : Fin 8 => tdpE8Root i))) :
    (foldedDiagramOfRoots tdpIsometry (Set.range (fun i : Fin 8 => tdpE8Root i))).edges
        (tdpE8Fold hroot 2) (tdpE8Fold hroot 3) = 1 / 4 := by
  rw [tdpFoldedE8Diagram_edges_foldedRootSet, e8GramMatrix_eq]
  norm_num

end LeanCategories.Lattices.Valued

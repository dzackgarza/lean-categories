/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingTdpE8NoFoldDropped

/-!
# Probe: no `E₈` fold is dropped

The two preceding files carried "no fold is dropped" as a hypothesis. The probes here decide
that for the `E₈` family of `T_dP` it is discharged, and that the published adjacent weight
survives with no hypotheses at Definition 3.7's indexing.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- Every folded `E₈` simple root is in Definition 3.7's set — no hypothesis. -/
example (i : Fin 8) :
    (⟨foldedVector tdpIsometry (tdpE8Root i),
      foldedVector_mem_fixed tdpIsometry tdpIsometry_mul_self (tdpE8Root i)⟩ :
        involutionFixedSubmodule tdpIsometry) ∈
      foldedRootSet tdpIsometry (Set.range tdpE8Family) :=
  tdpE8_mem_foldedRootSet i

/-- The published adjacent weight, at Definition 3.7's vertices, with nothing assumed. -/
example :
    (foldedDiagramOfRoots tdpIsometry (Set.range tdpE8Family)).edges
        (tdpE8Fold tdpE8_mem_foldedRootSet 2) (tdpE8Fold tdpE8_mem_foldedRootSet 3) = 1 / 4 := by
  rw [tdpFoldedE8Diagram_edges_foldedRootSet', e8GramMatrix_eq]
  norm_num

end LeanCategories.Lattices.Valued

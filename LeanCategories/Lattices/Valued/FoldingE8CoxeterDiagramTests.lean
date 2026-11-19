/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingDiagram

/-!
# Probe for the named folded diagram, on the smallest input that decides it

`tdpFoldedE8Diagram` packages the worked folded diagram of AEGS Lemma 3.9 as an actual
`CoxeterDiagram (Fin 8)` rather than an edge formula. The probe reads its two distinguished weights
off the diagram object: an `E₈` edge is `1/4` and an orthogonal pair is `0`.
-/

@[expose] public section

namespace LeanCategories.Lattices.Valued

/-- An `E₈` edge of the folded diagram has weight `1/4`. -/
example : tdpFoldedE8Diagram.edges 2 3 = 1 / 4 :=
  tdpFoldedE8Diagram_adjacent

/-- Two vertices that were orthogonal in `E₈` stay orthogonal. -/
example : tdpFoldedE8Diagram.edges 0 1 = 0 :=
  tdpFoldedE8Diagram_orthogonal

#print axioms tdpFoldedE8Diagram_edges_formula

end LeanCategories.Lattices.Valued

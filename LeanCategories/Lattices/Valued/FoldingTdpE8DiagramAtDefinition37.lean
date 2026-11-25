/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingChamberTraceAtDefinition37
public import LeanCategories.Lattices.Valued.FoldingDiagram

/-!
# The worked `E₈` folded diagram is Definition 3.7's diagram (`#116`)

Item 5 of the acceptance asks for "one worked declaration from a published folded diagram". The
declaration is `tdpFoldedE8Diagram` (`FoldingDiagram.lean`), the `E₈` block of `T_dP` folding to
`E₈(2)` — AEGS Lemma 3.9 and Figure 7 (**printed pp. 13–14**). But `tdpFoldedE8Diagram` is built
from
`foldedCoxeterDiagram`, the **family-indexed** form, while Definition 3.7's object is
`foldedDiagramOfRoots`, indexed by the surviving folds `{v // v ∈ foldedRootSet g R}`.

This file identifies them: when no fold is dropped, the two have the same edge weight at
corresponding vertices, so the worked declaration *is* Definition 3.7's diagram for the published
family.

* `tdpFoldedE8Diagram_edges_eq_foldedDiagramOfRoots` — the identification, vertex by vertex;
* `tdpFoldedE8Diagram_edges_foldedRootSet` — the resulting edge formula at Definition 3.7's
  vertices, `(gᵢⱼ)² / 4` in the `E₈` Gram matrix, which is what "the `E₈` block folds to `E₈(2)`"
  says.

The "no fold is dropped" hypothesis is Lemma 3.4 forward's content for this family, carried
explicitly here rather than assumed silently (the same shape as
`FoldingChamberTraceAtDefinition37`).

## LC-09 record

Queries run before writing: `"foldedCoxeterDiagram"` (0 files), `"Coxeter diagram folding
involution"` (1 file, `TauCeti/GroupTheory/Presentation/Coxeter.lean` — group presentations, not
folded diagrams),
`"folded root set diagram"` (1 file shown, `TauCeti/LinearAlgebra/RootSystem/OrbitSum.lean` — orbit
sums, no folding). Nothing to port.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, *Compact moduli of Enriques surfaces of
  degree 2*,
  Nagoya Math. J. 259 (2025), arXiv:2312.03638v2: Definition 3.7 **printed p. 12**; Lemma 3.9 and
  Figures 7–8, the `E₈` block folding to `E₈(2)`, **printed pp. 13–14**.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The surviving folds of the `E₈` family, as elements of Definition 3.7's set. -/
noncomputable abbrev tdpE8Fold (hroot : ∀ i : Fin 8,
    (⟨foldedVector tdpIsometry (tdpE8Root i),
      foldedVector_mem_fixed tdpIsometry tdpIsometry_mul_self (tdpE8Root i)⟩ :
        involutionFixedSubmodule tdpIsometry) ∈
      foldedRootSet tdpIsometry (Set.range (fun i : Fin 8 => tdpE8Root i)))
    (i : Fin 8) :
    {v : involutionFixedSubmodule tdpIsometry //
      v ∈ foldedRootSet tdpIsometry (Set.range (fun i : Fin 8 => tdpE8Root i))} :=
  ⟨⟨foldedVector tdpIsometry (tdpE8Root i),
    foldedVector_mem_fixed tdpIsometry tdpIsometry_mul_self (tdpE8Root i)⟩, hroot i⟩

/-- **The worked declaration is Definition 3.7's diagram**: the edge weights agree at corresponding
vertices. -/
theorem tdpFoldedE8Diagram_edges_eq_foldedDiagramOfRoots
    (hroot : ∀ i : Fin 8,
      (⟨foldedVector tdpIsometry (tdpE8Root i),
        foldedVector_mem_fixed tdpIsometry tdpIsometry_mul_self (tdpE8Root i)⟩ :
          involutionFixedSubmodule tdpIsometry) ∈
        foldedRootSet tdpIsometry (Set.range (fun i : Fin 8 => tdpE8Root i)))
    (i j : Fin 8) :
    tdpFoldedE8Diagram.edges i j =
      (foldedDiagramOfRoots tdpIsometry (Set.range (fun i : Fin 8 => tdpE8Root i))).edges
        (tdpE8Fold hroot i) (tdpE8Fold hroot j) := by
  rw [tdpFoldedE8Diagram, foldedCoxeterDiagram_edges, foldedDiagramOfRoots_edges]
  rfl

/-- **The edge formula at Definition 3.7's vertices**: `(gᵢⱼ)² / 4` in the `E₈` Gram matrix — the
`E₈(2)` of AEGS Lemma 3.9 and Figure 7 (**printed pp. 13–14**). -/
theorem tdpFoldedE8Diagram_edges_foldedRootSet
    (hroot : ∀ i : Fin 8,
      (⟨foldedVector tdpIsometry (tdpE8Root i),
        foldedVector_mem_fixed tdpIsometry tdpIsometry_mul_self (tdpE8Root i)⟩ :
          involutionFixedSubmodule tdpIsometry) ∈
        foldedRootSet tdpIsometry (Set.range (fun i : Fin 8 => tdpE8Root i)))
    (i j : Fin 8) :
    (foldedDiagramOfRoots tdpIsometry (Set.range (fun i : Fin 8 => tdpE8Root i))).edges
        (tdpE8Fold hroot i) (tdpE8Fold hroot j) = (e8GramMatrix i j : ℚ) ^ 2 / 4 := by
  rw [← tdpFoldedE8Diagram_edges_eq_foldedDiagramOfRoots hroot i j,
    tdpFoldedE8Diagram_edges_formula]

end LeanCategories.Lattices.Valued

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingTdpE8DiagramAtDefinition37
public import LeanCategories.Lattices.Valued.FoldingTdpHsubFails

/-!
# No `E₈` fold is dropped (`#116`)

The last two files state AEGS Lemma 3.8's trace identity and the identity of the worked `E₈` diagram
with Definition 3.7's diagram, each under "no fold is dropped". For the `E₈` family of `T_dP` that
hypothesis is not extra data: it is AEGS Lemma 3.4's forward direction (**printed pp. 11–12**)
applied to the printed diagram, and this file discharges it.

* `tdpE8_mem_foldedRootSet` — the fold of every `E₈` simple root is a member of Definition 3.7's
  folded root set, from three facts about the printed roots: square `−2` (`tdpE8Root_square`),
  hence reflective; negative square; and orthogonal to its image (`tdpE8Root_pairing_image`). The
  conversion from `negativeReflectiveRoots` to `foldedRootSet` rewrites the same three conditions.
* `tdpFoldedE8Diagram_edges_foldedRootSet'` — the edge formula at Definition 3.7's vertices with
  **no** "no fold is dropped" hypothesis, `(gᵢⱼ)² / 4`;
* `chamberOf_folded_trace_tdpE8` — Lemma 3.8's trace identity at Definition 3.7's set with **no**
  "no fold is dropped" hypothesis, for the `E₈` family of `T_dP`.

What is still carried, and is data of the chamber rather than of the folding:
`IsChamberWithWalls L t R` for the wall set `R`, i.e. the printed chamber of `T_dP` (Figure 5,
**printed p. 11**), which the development does not yet have as a family of roots.

## LC-09 record

Queries run before writing: `"foldedWallFamily"` (0 files), `"reflective root orthogonal to image
folds to root"` (0 files), `"root of invariant sublattice fold"` (1 file shown, a `LeanBridge`
`ZLattice` module about perfect lattices, no folding). Nothing to port.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, *Compact moduli of Enriques surfaces of
  degree 2*,
  Nagoya Math. J. 259 (2025), arXiv:2312.03638v2: Figure 5 **printed p. 11**; Definition 3.7 and
  Lemma 3.8 **printed p. 12**; Lemma 3.9 and Figures 7–8 **printed pp. 13–14**.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The `E₈` family of wall roots of `T_dP`, as a function. -/
abbrev tdpE8Family : Fin 8 → tdpFiniteLattice.obj.obj.carrier := fun i => tdpE8Root i

/-- **No `E₈` fold is dropped**: each folded simple root is a member of Definition 3.7's set. -/
theorem tdpE8_mem_foldedRootSet (i : Fin 8) :
    (⟨foldedVector tdpIsometry (tdpE8Root i),
      foldedVector_mem_fixed tdpIsometry tdpIsometry_mul_self (tdpE8Root i)⟩ :
        involutionFixedSubmodule tdpIsometry) ∈
      foldedRootSet tdpIsometry (Set.range tdpE8Family) := by
  have hfold := foldedWallFamily_mem_negativeReflectiveRoots tdpIsometry
    tdpIsometry_mul_self tdpE8Family
    (fun i => isReflectiveRoot_of_pairing_self_eq_neg_two (tdpE8Root_square i))
    (fun i => by rw [tdpE8Root_square i]; norm_num)
    (fun i => Or.inr (by rw [tdpIsometry_tdpE8Root i]; exact tdpE8Root_pairing_image i)) i
  have hroot := (mem_negativeReflectiveRoots_iff (invariantFixedLattice tdpIsometry)).mp hfold
  refine (mem_foldedRootSet_iff tdpIsometry (Set.range tdpE8Family) _).mpr ⟨?_, hroot.2, ?_⟩
  · exact ⟨tdpE8Root i, ⟨i, rfl⟩, rfl⟩
  · exact hroot.1.dvd_two_mul

/-- **The `E₈` edge formula at Definition 3.7's vertices, with no hypotheses.** -/
theorem tdpFoldedE8Diagram_edges_foldedRootSet' (i j : Fin 8) :
    (foldedDiagramOfRoots tdpIsometry (Set.range tdpE8Family)).edges
        (tdpE8Fold tdpE8_mem_foldedRootSet i) (tdpE8Fold tdpE8_mem_foldedRootSet j) =
      (e8GramMatrix i j : ℚ) ^ 2 / 4 :=
  tdpFoldedE8Diagram_edges_foldedRootSet tdpE8_mem_foldedRootSet i j

/-- **AEGS Lemma 3.8's trace identity at Definition 3.7's set for the `E₈` family of `T_dP`, with no
"no fold is dropped" hypothesis.** -/
theorem chamberOf_folded_trace_tdpE8
    (t : (realForm tdpFiniteLattice).obj.carrier)
    (hpos : (integralSignature tdpFiniteLattice).1 = 1)
    (ht : 0 < realFormQuadratic tdpFiniteLattice t)
    (hR : IsChamberWithWalls tdpFiniteLattice t (Set.range tdpE8Family))
    {v : tdpFiniteLattice.obj.obj.carrier}
    (hv : toRealForm tdpFiniteLattice v ∈
      rootInteriorCone tdpFiniteLattice t (Set.range tdpE8Family)) :
    chamberOf tdpFiniteLattice t (toRealForm tdpFiniteLattice v) ∩
        (realFormFixedPart tdpIsometry : Set (realForm tdpFiniteLattice).obj.carrier) =
      rootInteriorCone tdpFiniteLattice t (Set.range (fun v : {v // v ∈
        foldedRootSet tdpIsometry (Set.range tdpE8Family)} =>
          ((v.1 : involutionFixedSubmodule tdpIsometry) : tdpFiniteLattice.obj.obj.carrier))) ∩
        (realFormFixedPart tdpIsometry : Set (realForm tdpFiniteLattice).obj.carrier) :=
  chamberOf_folded_trace_foldedRootSet tdpIsometry tdpIsometry_mul_self (Set.range tdpE8Family)
    (fun v hv => by
      obtain ⟨i, rfl⟩ := hv
      exact tdpE8_mem_foldedRootSet i) t hpos ht hR hv

end LeanCategories.Lattices.Valued

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.VinbergE10Roots

/-!
# The `E₁₀` diagram has no non-trivial symmetry, so its chamber no non-trivial involution (`#116`)

The only explicit Lorentzian chamber in this repository is `E₁₀(2)`'s
(`VinbergE10Chamber.e10_isChamberWithWalls`), and the non-vacuity certificate of
`FoldingWitness.lean` runs at the identity involution, which is the only chamber-preserving one for
the hyperbolic plane. Whether `E₁₀(2)` could carry a *non-trivial* instance was open; this file
settles it negatively.

The `E₁₀` diagram of `VinbergE10Roots.e10Adjacency` is a tree with adjacency
`0–8, 0–9, 1–3, 2–4, 3–4, 4–5, 5–6, 6–7, 7–8`. Its degrees are

| node | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|---|
| degree | 2 | 1 | 1 | 2 | **3** | 2 | 2 | 2 | 2 | 1 |

so node `4` is the **unique** branch point (`e10_branch_point`, `e10_no_other_branch`, both by
`decide`). Its three branches are the leaf `2`, the two-node arm `3–1`, and the six-node chain
`5–6–7–8–0–9`; their lengths `1, 2, 6` are pairwise different, so every automorphism of the diagram
fixes node `4` and each branch pointwise — the automorphism group is trivial. (The branch-length
step is a hand argument, not formalized; the two degree facts above are.)

Since the stabilizer of a chamber of a reflection group in `O(M)` injects into the diagram's
automorphism group, **`E₁₀(2)` admits no non-trivial chamber-preserving involution**, and it cannot
supply one for the joining theorem of `FoldingInvariantChamber.lean`. A non-trivial instance has to
come from `T_dP = U ⊕ U(2) ⊕ E₈ ⊕ E₈` with `I = -I_En` — the source's own setting, AEGS §3.8,
whose folded diagrams rest on the 19- and 22-vertex diagrams of its Figure 5, printed as pictures
and not tabulated.

## LC-09 record

Searched the repository for the `E₁₀` diagram's symmetries and for a lattice realization of a
diagram automorphism: `rg "e10Adjacency|e10Edge"` gives `VinbergE10Roots.lean:95-110` (the edge
list, nine edges for ten nodes, a tree) and no symmetry statement; `rg "automorphism"` over
`LeanCategories/Lattices/` gives the `CoxeterDiagram`/`RootPairing` permutation API only. Mathlib
has `CoxeterMatrix` with no graph-automorphism API for it. The Formalization Corpus returns no files
for "tree automorphism unique branch point". Nothing ported.

## References

* È. B. Vinberg, *The groups of unit elements of certain quadratic forms*, Mat. Sb. 87 (1972), §1
  (the `E₁₀` chamber), as formalized in `VinbergE10Chamber.lean`.
* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, arXiv:2312.03638v2, §3.8 (printed p. 13): the
  diagram involutions by which the `T^dP` diagrams are folded.
-/

@[expose] public section

namespace LeanCategories.Lattices.Valued

/-- The neighbours of node `4` in the `E₁₀` diagram. -/
theorem e10_branch_point :
    (Finset.univ.filter (fun j : Fin 10 => j ≠ 4 ∧ e10Cartan 4 j ≠ 0))
      = {2, 3, 5} := by
  decide

/-- No node other than `4` has three neighbours: the branch point is unique. -/
theorem e10_no_other_branch (i : Fin 10) (hi : i ≠ 4) :
    ¬ (Finset.univ.filter (fun j : Fin 10 => j ≠ i ∧ e10Cartan i j ≠ 0)).card = 3 := by
  fin_cases i
  · decide
  · decide
  · decide
  · decide
  · exact absurd rfl hi
  · decide
  · decide
  · decide
  · decide
  · decide

/-- The degrees of the `E₁₀` diagram's nodes. -/
theorem e10_degree (i : Fin 10) :
    (Finset.univ.filter (fun j : Fin 10 => j ≠ i ∧ e10Cartan i j ≠ 0)).card
      = ![2, 1, 1, 2, 3, 2, 2, 2, 2, 1] i := by
  fin_cases i <;> decide

end LeanCategories.Lattices.Valued

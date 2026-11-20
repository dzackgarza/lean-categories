/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.Folding
public import LeanCategories.Lattices.Valued.FoldingRootHypothesis

/-!
# Lemma 3.8's trace identity at Definition 3.7's set (`#116`)

`chamberOf_folded_trace` (`Folding.lean`) is AEGS Lemma 3.8 in the form the source proves it: inside
the invariant part of the real form, the folded roots cut out exactly the trace of the chamber of
`W(M)`. It is stated at `foldedRootImage`, the image of the wall set under folding — which is *not*
Definition 3.7's object, since that image also contains folds that are not roots of `M^σ`.

Definition 3.7 (**printed p. 12**) keeps only the folds that *are* roots of `Λ^{J=1}` = `M^σ`. When
none is dropped — which is what AEGS Lemma 3.4's forward direction supplies, and what
`foldedWallFamily_mem_negativeReflectiveRoots` proves for a wall family
(`FoldingRootHypothesis.lean`) — the two sets coincide:

* `foldedRootImage_eq_range` — the folded image is the range of Definition 3.7's set, given that
every
  folded wall is a root of `M^σ`;
* `chamberOf_folded_trace_foldedRootSet` — Lemma 3.8's trace identity at Definition 3.7's set.

Why this is the acceptance's object and not a weakening: the statement is the source's own, at the
source's own set, and it carries no hypothesis beyond "no fold is dropped". In particular it does
not
need the ambient-expansion inputs (`hsub`, `hamb`) that the `IsChamberWithWalls` route requires and
that fail for `T_dP` (`FoldingTdpHsubFails.lean`).

## LC-09 record

Repository: `rg "foldedRootImage_eq_range|trace_foldedRootSet"` nothing;
`foldedRootSet_subset_image` gives one inclusion only, at the subtype range, and nothing gives the
other. Mathlib has no statement
about folded root sets. Corpus: nothing. No port.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, *Compact moduli of Enriques surfaces of degree
  2*,
  Nagoya Math. J. 259 (2025), arXiv:2312.03638v2: Definition 3.3 **printed p. 11**; Lemma 3.4 and
  Definition 3.7 **printed p. 12**; Lemma 3.8 **printed p. 12**.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **The folded image is Definition 3.7's set**, as a set of ambient vectors, when no fold is
dropped. -/
theorem foldedRootImage_eq_range (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    (R : Set L.obj.obj.carrier)
    (hroot : ∀ v ∈ R,
      (⟨foldedVector g v, foldedVector_mem_fixed g hg v⟩ : involutionFixedSubmodule g) ∈
        foldedRootSet g R) :
    Set.range (fun v : {v // v ∈ foldedRootSet g R} =>
        ((v.1 : involutionFixedSubmodule g) : L.obj.obj.carrier)) = foldedRootImage g R := by
  refine Set.Subset.antisymm (foldedRootSet_subset_image g R) ?_
  rintro x ⟨y, hy, rfl⟩
  exact ⟨⟨_, hroot y hy⟩, rfl⟩

/-- **AEGS Lemma 3.8 at Definition 3.7's folded root set**: the folded roots, filtered as the source
filters them, cut out exactly the trace of the chamber. -/
theorem chamberOf_folded_trace_foldedRootSet (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    (R : Set L.obj.obj.carrier)
    (hroot : ∀ v ∈ R,
      (⟨foldedVector g v, foldedVector_mem_fixed g hg v⟩ : involutionFixedSubmodule g) ∈
        foldedRootSet g R)
    (t : (realForm L).obj.carrier) (hpos : (integralSignature L).1 = 1)
    (ht : 0 < realFormQuadratic L t) (hR : IsChamberWithWalls L t R)
    {v : L.obj.obj.carrier} (hv : toRealForm L v ∈ rootInteriorCone L t R) :
    chamberOf L t (toRealForm L v) ∩ (realFormFixedPart g : Set (realForm L).obj.carrier) =
      rootInteriorCone L t (Set.range (fun v : {v // v ∈ foldedRootSet g R} =>
        ((v.1 : involutionFixedSubmodule g) : L.obj.obj.carrier))) ∩
        (realFormFixedPart g : Set (realForm L).obj.carrier) := by
  rw [foldedRootImage_eq_range g hg R hroot]
  exact chamberOf_folded_trace g t hpos ht hR hv

end LeanCategories.Lattices.Valued

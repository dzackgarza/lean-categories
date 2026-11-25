/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingDiagram

/-!
# The folded diagram is the orbit diagram (`#116`)

`Folding.lean`'s Definition 3.7 keeps only the folds that are roots of `M^σ`
(`foldedRootSet`), and `FoldingDiagram.lean` proves that the fold is constant on the orbits of a
diagram involution (`actsThrough_foldedVector_eq`) — which is what makes the folded diagram smaller
than the diagram it comes from. This file closes the loop: **the vertices of the folded diagram are
fixed by the involution**, so the diagram involution acts trivially on the folded diagram, and
folding
has already quotiented it out.

* `foldedVector_folded` — the fold is idempotent on the folded set: folding a vertex returns it, so
  the diagram involution induced by `g` acts trivially on the folded diagram (one vertex per orbit).
* `foldedRootSet_fold_mem` — hence the folded root set is closed under folding, with its vertices as
  the fixed points.
* `range_foldedDiagramOfRoots_eq` — **the two spellings of Definition 3.7 agree**: when every fold
of
  a root family is a root of `M^σ`, no fold is dropped, and the set-indexed diagram
  `foldedDiagramOfRoots` has exactly the vertex set of the family-indexed `foldedCoxeterDiagram`.

## LC-09 record

Searched for "involution acts trivially on the orbit space" and for the statement that the fold of a
fold is itself: `rg "foldedVector"` over `LeanCategories/Lattices/Valued/` gives `Folding.lean`'s
Definition 3.3 and its lemmas (`foldedVector_of_fixed`, `foldedVector_of_not_fixed`,
`foldedVector_mem_fixed`, `foldedVector_invariant`) and `FoldingDiagram.lean`'s orbit constancy —
none states idempotence of the fold, which is one line from `foldedVector_mem_fixed` but is what the
"one vertex per orbit" claim needs. Mathlib has nothing on folding. The Formalization Corpus returns
no files for "fold idempotent invariant sublattice orbit". Nothing ported.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, arXiv:2312.03638v2, §3.7 (printed p. 12):
  Definition 3.3 and Definition 3.7.
-/

@[expose] public section

open QuadraticMap
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **The fold is idempotent on the folded set**: folding a vertex of the folded diagram returns
that vertex. So folding is an idempotent operation on the roots, with the folded roots as its fixed
points — the precise sense in which the folded diagram has one vertex per orbit, not one per root.
-/
theorem foldedVector_folded (g : OrthogonalGroup L.obj)
    (R : Set L.obj.obj.carrier) {v : involutionFixedSubmodule g}
    (_hv : v ∈ foldedRootSet (L := L) g R) :
    foldedVector g (v : L.obj.obj.carrier) = v :=
  foldedVector_of_fixed g ((mem_involutionFixedSubmodule_iff g).mp v.2)

/-- **The folded root set is closed under folding**: folding a vertex returns it, as an element of
the
invariant lattice. -/
theorem foldedRootSet_fold_mem (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    (R : Set L.obj.obj.carrier) {v : involutionFixedSubmodule g}
    (hv : v ∈ foldedRootSet (L := L) g R) :
    (⟨foldedVector g (v : L.obj.obj.carrier), foldedVector_mem_fixed g hg _⟩ :
        involutionFixedSubmodule g) = v :=
  Subtype.ext (foldedVector_folded g R hv)

/-- **Definition 3.7's diagram, indexed by the surviving folds, has exactly the vertex set of the
folded family.** When every fold of a root family `r` has negative square and integral reflection in
`M^σ`, no fold is dropped, so the set-indexed diagram `foldedDiagramOfRoots` and the family-indexed
one `foldedCoxeterDiagram` have the same vertices. -/
theorem range_foldedDiagramOfRoots_eq (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    {ι : Type*} (r : ι → L.obj.obj.carrier)
    (hneg : ∀ i, L.obj.obj.pairing (foldedRootFamily g r i) (foldedRootFamily g r i) < 0)
    (hrefl : ∀ i, ∀ x : involutionFixedSubmodule g,
      L.obj.obj.pairing (foldedRootFamily g r i) (foldedRootFamily g r i) ∣
        2 * L.obj.obj.pairing (foldedRootFamily g r i) (x : L.obj.obj.carrier)) :
    Set.range (fun v : {v // v ∈ foldedRootSet (L := L) g (Set.range r)} =>
        ((v.1 : involutionFixedSubmodule g) : L.obj.obj.carrier))
      = Set.range (foldedRootFamily g r) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨v, rfl⟩
    have himg : ((v.1 : involutionFixedSubmodule g) : L.obj.obj.carrier)
        ∈ foldedRootImage g (Set.range r) := ((mem_foldedRootSet_iff g (Set.range r) v.1).mp v.2).1
    rwa [foldedRootImage_range] at himg
  · rintro _ ⟨i, rfl⟩
    have himg : foldedRootFamily g r i ∈ foldedRootImage g (Set.range r) := by
      rw [foldedRootImage_range]; exact ⟨i, rfl⟩
    refine ⟨⟨⟨foldedRootFamily g r i, foldedVector_mem_fixed g hg (r i)⟩, ?_⟩, rfl⟩
    exact ⟨himg, hneg i, hrefl i⟩

end LeanCategories.Lattices.Valued

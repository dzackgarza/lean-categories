/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingDiagramOrbits
public import LeanCategories.Lattices.Valued.FoldingWitness

/-!
# Probes for `FoldingDiagramOrbits`, on the smallest input that decides it

The claims are about the folded root set, so the deciding input is one worked folded root:
the hyperbolic plane at the identity involution, where the folded root set is `{e - f}`
(`u_foldedRootSet_one`). There:

* folding it returns it (`foldedVector_folded`);
* the closure statement holds (`foldedRootSet_fold_mem`);
* the set-indexed and family-indexed spellings of Definition 3.7 have the same vertex set
  (`range_foldedDiagramOfRoots_eq`), on the one-root family `e - f`.

The non-vacuity point that matters: the identity is the *only* chamber-preserving involution of `U`,
so a non-trivial `g` cannot be tested here — which is why the lemmas are stated for arbitrary `g`
and only *probed* at the identity.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- Folding the vertex `e - f` returns it. -/
example : foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)
    (uRootFixed : hyperbolicPlaneFiniteLattice.obj.obj.carrier)
      = (uRootFixed : hyperbolicPlaneFiniteLattice.obj.obj.carrier) :=
  foldedVector_folded (L := hyperbolicPlaneFiniteLattice)
    (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot}
    (by rw [u_foldedRootSet_one]; exact Set.mem_singleton uRootFixed)

/-- The folded root set is closed under folding at its vertex. -/
example : (⟨foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)
      (uRootFixed : hyperbolicPlaneFiniteLattice.obj.obj.carrier),
      foldedVector_mem_fixed _ (one_mul 1) _⟩ :
        involutionFixedSubmodule (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) = uRootFixed :=
  foldedRootSet_fold_mem (L := hyperbolicPlaneFiniteLattice)
    (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) (one_mul 1) {uRoot}
    (by rw [u_foldedRootSet_one]; exact Set.mem_singleton uRootFixed)

/-- The two spellings of Definition 3.7 have the same vertices when no fold is dropped: here the
family is the single root `e - f` of the hyperbolic plane. -/
example : Set.range (fun v : {v // v ∈ foldedRootSet (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) (Set.range ![uRoot])} =>
        ((v.1 : involutionFixedSubmodule (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) :
            hyperbolicPlaneFiniteLattice.obj.obj.carrier))
      = Set.range (foldedRootFamily (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) ![uRoot]) :=
  range_foldedDiagramOfRoots_eq (L := hyperbolicPlaneFiniteLattice)
    (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) (one_mul 1) ![uRoot]
    (fun i => by
      fin_cases i
      change hyperbolicPlaneFiniteLattice.obj.obj.pairing
        (foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRoot)
        (foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRoot) < 0
      have hfix : foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRoot
          = uRoot := foldedVector_of_fixed _ rfl
      rw [hfix, uRoot_square]
      norm_num)
    (fun i x => by
      fin_cases i
      change hyperbolicPlaneFiniteLattice.obj.obj.pairing
        (foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRoot)
        (foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRoot) ∣
          2 * hyperbolicPlaneFiniteLattice.obj.obj.pairing
            (foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRoot)
            (x : hyperbolicPlaneFiniteLattice.obj.obj.carrier)
      have hfix : foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRoot
          = uRoot := foldedVector_of_fixed _ rfl
      rw [hfix, uRoot_square]
      change (-2 : ℤ) ∣ 2 * hyperbolicPlaneFiniteLattice.obj.obj.pairing uRoot
        (x : hyperbolicPlaneFiniteLattice.obj.obj.carrier)
      rw [show hyperbolicPlaneFiniteLattice.obj.obj.pairing uRoot
          (x : hyperbolicPlaneFiniteLattice.obj.obj.carrier)
            = uRoot 0 * x.1 1 + uRoot 1 * x.1 0 from u_pairing_eq' _ _]
      simp only [uRoot_apply_zero, uRoot_apply_one, one_mul, neg_one_mul]
      exact ⟨x.1 0 - x.1 1, by ring⟩)

#print axioms foldedVector_folded
#print axioms foldedRootSet_fold_mem

end LeanCategories.Lattices.Valued

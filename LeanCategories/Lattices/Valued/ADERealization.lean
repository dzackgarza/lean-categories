/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DiagramShape
public import LeanCategories.Lattices.Valued.ReducedBasis

/-!
# ADE diagram realizations

The shape theorem records a path by a graph walk. This file supplies the representation boundary
needed by the realization theorem: a covering path gives an equivalence with a finite index type,
and reindexing the root-base basis along that equivalence gives the corresponding Gram matrix.
The construction is intrinsic until the final comparison with a named standard lattice.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

namespace FiniteProjectiveLatticeCat

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

namespace IsRootBase

variable {B : Set L.obj.obj.carrier}

/-- The vertices of a covering path, indexed by its vertices rather than by `ℕ`. -/
noncomputable def pathIndexMap {u v : B} {q : (rootBaseGraph L B).Walk u v}
    (_hcover : ∀ w : B, w ∈ q.support) : Fin (q.length + 1) → B :=
  fun i => q.getVert i

/-- A covering path gives an equivalence between its finite index set and the base. -/
noncomputable def pathIndexEquiv {u v : B} {q : (rootBaseGraph L B).Walk u v}
    (hq : q.IsPath) (hcover : ∀ w : B, w ∈ q.support) : Fin (q.length + 1) ≃ B := by
  refine Equiv.ofBijective (pathIndexMap hcover) ?_
  constructor
  · intro i j hij
    apply Fin.ext
    apply hq.getVert_injOn (Nat.le_of_lt_succ (by simpa using i.isLt))
      (Nat.le_of_lt_succ (by simpa using j.isLt))
    exact hij
  · intro w
    obtain ⟨i, rfl, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hcover w)
    exact ⟨⟨i, Nat.lt_succ_of_le hi⟩, rfl⟩

/-- Reindex the root-base basis by the vertices of a covering path. -/
noncomputable def pathBasis {u v : B} {q : (rootBaseGraph L B).Walk u v}
    (hB : IsRootBase L B) (hq : q.IsPath) (hcover : ∀ w : B, w ∈ q.support) :
    Module.Basis (Fin (q.length + 1)) ℤ L.obj.obj.carrier :=
  hB.basis.reindex (pathIndexEquiv hq hcover).symm

/-! ## The path Gram matrix -/

/-- The Gram matrix prescribed by a path of simple roots. -/
def pathGramMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦ if i = j then -2 else
    if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0

@[simp]
theorem pathGramMatrix_diag (n : ℕ) (i : Fin n) : pathGramMatrix n i i = -2 := by
  simp [pathGramMatrix]

/-- The reindexed basis of a path has its graph Gram matrix. -/
theorem gramMatrix_pathBasis {u v : B} {q : (rootBaseGraph L B).Walk u v}
    (hL : IsNegativeDefiniteLattice L) (hB : IsRootBase L B) (hq : q.IsPath)
    (hcover : ∀ w : B, w ∈ q.support) :
    gramMatrix L.obj (hB.pathBasis hq hcover) = pathGramMatrix (q.length + 1) := by
  classical
  ext i j
  simp only [gramMatrix, LinearMap.BilinForm.toMatrix_apply, BilinModuleCat.bilinMap_apply]
  rw [pathBasis, Module.Basis.reindex_apply, Module.Basis.reindex_apply,
    IsRootBase.basis_apply, IsRootBase.basis_apply]
  change L.obj.obj.pairing (q.getVert i) (q.getVert j) = _
  by_cases hij : i = j
  · subst j
    simp [pathGramMatrix, hB.pairing_self]
  · have hne : (i : ℕ) ≠ j := by
      intro h
      exact hij (Fin.ext h)
    have hi : (i : ℕ) ≤ q.length := Nat.le_of_lt_succ (by simpa using i.isLt)
    have hj : (j : ℕ) ≤ q.length := Nat.le_of_lt_succ (by simpa using j.isLt)
    have hvertices_ne : q.getVert i ≠ q.getVert j := by
      intro h
      exact hij (Fin.ext (hq.getVert_injOn hi hj h))
    by_cases hsucc : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
    · have hadj : (rootBaseGraph L B).Adj (q.getVert i) (q.getVert j) := by
        rcases hsucc with hsucc | hsucc
        · rw [← hsucc]
          exact q.adj_getVert_succ (by omega)
        · have hjlt : (j : ℕ) < q.length := by
            exact lt_of_lt_of_le (by omega) hi
          rw [← hsucc]
          exact (q.adj_getVert_succ hjlt).symm
      rw [hB.pairing_eq_one_of_adj hadj]
      simp [pathGramMatrix, hij, hsucc]
    · have hnotadj : ¬(rootBaseGraph L B).Adj (q.getVert i) (q.getVert j) := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact notAdj_getVert (hB.isAcyclic_rootBaseGraph hL) hq
            (a := (i : ℕ)) (b := (j : ℕ)) (by omega) hj
        · intro hadj
          exact notAdj_getVert (hB.isAcyclic_rootBaseGraph hL) hq
            (a := (j : ℕ)) (b := (i : ℕ)) (by omega) hi hadj.symm
      rw [pairing_eq_zero_of_notAdj hvertices_ne hnotadj]
      simp [pathGramMatrix, hij, hsucc]

end IsRootBase

end FiniteProjectiveLatticeCat

end LeanCategories.Lattices.Valued

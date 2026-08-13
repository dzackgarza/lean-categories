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

theorem pathGramMatrix_eq_aRootGramMatrix (n : ℕ) :
    pathGramMatrix n = aRootGramMatrix n := by
  classical
  ext i j
  have hvec (r : Fin n) (k : Fin (n + 1)) :
      aRootVector n r k =
        (if k = r.castSucc then (1 : ℤ) else 0) -
          (if k = r.succ then 1 else 0) := by
    by_cases hcast : k = r.castSucc
    · subst k
      have hne : r.castSucc ≠ r.succ := by simp [Fin.ext_iff]
      simp [aRootVector, hne]
    · by_cases hsucc : k = r.succ
      · subst k
        have hne : r.succ ≠ r.castSucc := by simpa using hcast
        simp [aRootVector, hcast, hne]
      · have hcast' : k.val ≠ r.val := by
          intro h
          exact hcast (Fin.ext h)
        have hsucc' : k.val ≠ r.val + 1 := by
          intro h
          exact hsucc (Fin.ext h)
        simp [aRootVector, hcast, hsucc, hcast', hsucc', Fin.ext_iff]
  simp only [aRootGramMatrix]
  simp_rw [hvec i, hvec j]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, neg_sub]
  by_cases hij : i = j
  · subst j
    have hne : i.succ ≠ i.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    simp [pathGramMatrix, hne, hne.symm]
  · have hij' : i.val ≠ j.val := by
      intro h
      exact hij (Fin.ext h)
    have hji : j ≠ i := Ne.symm hij
    have hne_i : i.succ ≠ i.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    by_cases hnext : i.val + 1 = j.val
    · have hprev : ¬j.val + 1 = i.val := by omega
      have hleft : j.succ ≠ i.castSucc := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
        omega
      have hright : j.castSucc = i.succ := by
        apply Fin.ext
        simp [hnext]
      simp [pathGramMatrix, hnext, hprev, hij, hji, hij', hleft, hright, hne_i]
    · by_cases hprev : j.val + 1 = i.val
      · have hnext' : ¬i.val + 1 = j.val := by omega
        have hleft : j.succ = i.castSucc := by
          apply Fin.ext
          simp [hprev]
        have hright : j.castSucc ≠ i.succ := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
          omega
        simp [pathGramMatrix, hnext', hprev, hij, hji, hij', hleft, hright, hne_i,
          hne_i.symm]
      · have hleft : j.succ ≠ i.castSucc := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
          omega
        have hright : j.castSucc ≠ i.succ := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
          omega
        simp [pathGramMatrix, hnext, hprev, hij, hji, hij', hleft, hright, hne_i]

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

/-- A path-shaped root base presents the standard type-`A` lattice of the same rank. -/
noncomputable def isoARootFiniteLatticeOfPathBasis {u v : B}
    {q : (rootBaseGraph L B).Walk u v}
    (hL : IsNegativeDefiniteLattice L) (hB : IsRootBase L B) (hq : q.IsPath)
    (hcover : ∀ w : B, w ∈ q.support) :
    aRootFiniteLattice (q.length + 1) ≅ L := by
  have hiso := L.isoFiniteLatticeOfGramMatrix (hB.pathBasis hq hcover)
  have hmatrix : gramMatrix L.obj (hB.pathBasis hq hcover) =
      aRootGramMatrix (q.length + 1) :=
    (gramMatrix_pathBasis hL hB hq hcover).trans (pathGramMatrix_eq_aRootGramMatrix _)
  simpa [aRootFiniteLattice, hmatrix] using hiso

/-! ## Three-arm stars -/

/-- Indices for a branch vertex and the vertices on three finite arms. -/
inductive StarIndex (k : Fin 3 → ℕ)
  | branch
  | arm (t : Fin 3) (i : Fin (k t))
  deriving DecidableEq, Fintype

/-- The vertex of a star indexed by `StarIndex`. -/
def starVertex {c : B} (x : Fin 3 → ℕ → B) (a : StarIndex k) : B :=
  match a with
  | .branch => c
  | .arm t i => x t i

theorem starVertex_injective {c : B} {x : Fin 3 → ℕ → B} {k : Fin 3 → ℕ}
    (hstar : IsThreeArmStar L B c x k) :
    Function.Injective (starVertex (c := c) (k := k) x) := by
  intro a b hab
  cases a with
  | branch =>
      cases b with
      | branch => rfl
      | arm t i =>
          exfalso
          exact hstar.ne_branch t i (by exact i.isLt) hab.symm
  | arm t i =>
      cases b with
      | branch =>
          exfalso
          exact hstar.ne_branch t i (by exact i.isLt) hab
      | arm u j =>
          change x t i = x u j at hab
          by_cases htu : t = u
          · subst u
            by_cases hij : i = j
            · subst j
              rfl
            · have hself := hstar.isArm t |>.pairing_self i i.isLt
              have hlt : i.val < j.val ∨ j.val < i.val := by omega
              rcases hlt with hlt | hlt
              · by_cases hnext : i.val + 1 = j.val
                · have hadj := hstar.isArm t |>.pairing_succ i (by omega)
                  have hsame : L.obj.obj.pairing (x t i : L.obj.obj.carrier)
                      (x t i : L.obj.obj.carrier) = 1 := by
                    simpa [hnext, hab] using hadj
                  omega
                · have hfar := hstar.isArm t |>.pairing_far i j (by omega) j.isLt
                  have hsame : L.obj.obj.pairing (x t i : L.obj.obj.carrier)
                      (x t i : L.obj.obj.carrier) = 0 := by
                    simpa [hab] using hfar
                  omega
              · by_cases hnext : j.val + 1 = i.val
                · have hadj := hstar.isArm t |>.pairing_succ j (by omega)
                  have hsame : L.obj.obj.pairing (x t j : L.obj.obj.carrier)
                      (x t j : L.obj.obj.carrier) = 1 := by
                    simpa [hnext, hab] using hadj
                  have hselfj := hstar.isArm t |>.pairing_self j j.isLt
                  omega
                · have hfar := hstar.isArm t |>.pairing_far j i (by omega) i.isLt
                  have hsame : L.obj.obj.pairing (x t j : L.obj.obj.carrier)
                      (x t j : L.obj.obj.carrier) = 0 := by
                    simpa [hab] using hfar
                  have hselfj := hstar.isArm t |>.pairing_self j j.isLt
                  omega
          · have hcross := hstar.pairing_arm t u htu i i.isLt j j.isLt
            have hself := hstar.isArm t |>.pairing_self i i.isLt
            have hsame : L.obj.obj.pairing (x t i : L.obj.obj.carrier)
                (x t i : L.obj.obj.carrier) = 0 := by
              simpa [hab] using hcross
            omega

/-- A covering star gives an equivalence between its finite index type and the root base. -/
noncomputable def starIndexEquiv {c : B} {x : Fin 3 → ℕ → B} {k : Fin 3 → ℕ}
    (hstar : IsThreeArmStar L B c x k)
    (hcover : ∀ w : B, w = c ∨ ∃ t, ∃ i < k t, x t i = w) :
    StarIndex k ≃ B := by
  refine Equiv.ofBijective (starVertex (c := c) (k := k) x) ?_
  constructor
  · exact starVertex_injective hstar
  · intro w
    rcases hcover w with rfl | ⟨t, i, hi, rfl⟩
    · exact ⟨.branch, rfl⟩
    · exact ⟨.arm t ⟨i, hi⟩, rfl⟩

/-- Reindex the root-base basis by the vertices of a covering star. -/
noncomputable def starBasis {c : B} {x : Fin 3 → ℕ → B} {k : Fin 3 → ℕ}
    (hB : IsRootBase L B)
    (hstar : IsThreeArmStar L B c x k)
    (hcover : ∀ w : B, w = c ∨ ∃ t, ∃ i < k t, x t i = w) :
    Module.Basis (StarIndex k) ℤ L.obj.obj.carrier :=
  hB.basis.reindex (starIndexEquiv hstar hcover).symm

end IsRootBase

end FiniteProjectiveLatticeCat

end LeanCategories.Lattices.Valued

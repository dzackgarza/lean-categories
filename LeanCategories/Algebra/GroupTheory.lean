/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Outer automorphism groups

This file defines the outer automorphism group as the quotient of `MulAut G`
by the range of `MulAut.conj`.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

variable (G : Type u) [Group G]

namespace Subgroup

/-- The hypercenter, i.e. the supremum of the upper central series.
This is Dummit--Foote FC01-C06-U005. -/
def hypercenter : Subgroup G :=
  ⨆ n : ℕ, Subgroup.upperCentralSeries G n

end Subgroup

namespace Group

/-- A group is hypernilpotent when its hypercenter is the whole group. -/
def IsHypernilpotent : Prop := Subgroup.hypercenter G = ⊤

/-- The least index at which the derived series of a solvable group reaches
the trivial subgroup.  This is Dummit--Foote FC01-C06-U016. -/
noncomputable def solvableLength [_root_.Group.IsSolvable G] : ℕ := by
  classical
  exact Nat.find (_root_.Group.IsSolvable.solvable (G := G))

@[simp]
theorem derivedSeries_solvableLength_eq_bot [_root_.Group.IsSolvable G] :
    derivedSeries G (solvableLength G) = ⊥ := by
  classical
  exact Nat.find_spec (_root_.Group.IsSolvable.solvable (G := G))

theorem solvableLength_le [_root_.Group.IsSolvable G] {n : ℕ}
    (hn : derivedSeries G n = ⊥) : solvableLength G ≤ n := by
  classical
  exact Nat.find_min' (_root_.Group.IsSolvable.solvable (G := G)) hn

end Group

/-- The holomorph `G ⋊ Aut(G)`, with the automorphism group acting on `G` by
evaluation.  This is Dummit--Foote FC01-C05-U036. -/
abbrev holomorph : Type u :=
  SemidirectProduct G (MulAut G) (MonoidHom.id (MulAut G))

instance mulAutConjRangeNormal : (MulAut.conj : G →* MulAut G).range.Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro φ
  apply le_antisymm
  · intro ψ hψ
    rw [Subgroup.mem_map] at hψ
    rcases hψ with ⟨θ, hθ, rfl⟩
    rw [MonoidHom.mem_range] at hθ
    rcases hθ with ⟨g, rfl⟩
    change φ * MulAut.conj g * φ⁻¹ ∈ _
    have hconj : φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
      ext h
      simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]
    rw [hconj]
    exact MonoidHom.mem_range.mpr ⟨φ g, rfl⟩
  · intro ψ hψ
    rw [Subgroup.mem_map]
    rw [MonoidHom.mem_range] at hψ
    rcases hψ with ⟨g, rfl⟩
    refine ⟨MulAut.conj (φ⁻¹ g), MonoidHom.mem_range.mpr ⟨φ⁻¹ g, rfl⟩, ?_⟩
    change φ * MulAut.conj (φ⁻¹ g) * φ⁻¹ = _
    have hconj : φ * MulAut.conj (φ⁻¹ g) * φ⁻¹ = MulAut.conj (φ (φ⁻¹ g)) := by
      ext h
      simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]
    rw [hconj]
    simp

/-- The outer automorphism group `Aut(G) / Inn(G)`. -/
abbrev outerAutomorphismGroup : Type u :=
  MulAut G ⧸ (MulAut.conj : G →* MulAut G).range

/-- The canonical quotient map to the outer automorphism group. -/
abbrev outerAutomorphismGroupMap : MulAut G →* outerAutomorphismGroup G :=
  QuotientGroup.mk' (MulAut.conj : G →* MulAut G).range

end LeanCategories.Algebra

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Outer automorphism groups

This file defines the outer automorphism group as the quotient of `MulAut G`
by the range of `MulAut.conj`.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

variable (G : Type u) [Group G]

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

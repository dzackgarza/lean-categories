/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.WythoffCoarsenedFamily
public import Mathlib.Tactic

/-!
# Examples for #180

These are **examples**, on the smallest input that exhibits the construction: the rank-one
chamber of `ℝ` (one functional, no relevant vertex, trivial parabolic).  They show what the members
of the coarsened family are and exercise O2 on them.

They are not evidence for the general clauses.  O1 and O2 are proved for every datum in
`WythoffCoarsenedFamily`; O3 is *not* claimed there, and `swapDatum_not_maximalConesMeetInFaces`
shows that the maximal-cone intersection law it needs is **not** a consequence of the datum's
hypotheses, so no example could establish it either.
-/

@[expose] public section

namespace LeanCategories.Lattices.Valued

open PointedCone

/-- The single simple-root functional of the example: the identity of `ℝ`. -/
def examplePhi : Unit → ℝ →ₗ[ℝ] ℝ := fun _ => LinearMap.id

/-- The AET datum of the example: no irrelevant vertex, trivial reflection group. -/
def exampleDatum : WythoffCoarseningDatum examplePhi (∅ : Finset Unit) where
  W := ⊥
  WJ := ⊥
  WJ_le := le_rfl
  active_nonneg := by
    intro i _ g y hy
    have h1 : (g : ℝ ≃ₗ[ℝ] ℝ) = 1 := Subgroup.mem_bot.mp g.2
    rw [h1]
    simpa using hy i
  convex := by
    intro x hx y hy
    rw [aetGeneralizedChamber_bot] at *
    simp only [aetChamber, Set.mem_ofPred_eq] at hx hy ⊢
    intro i
    exact add_nonneg (hx i) (hy i)
  irrelevant_flips := by intro j hj; exact absurd hj (by simp)

/-- The maximal cone of the example is the closed half line `{x | 0 ≤ x}`. -/
theorem example_maximalCone : (exampleDatum.maximalCone : Set ℝ) = {x | 0 ≤ x} := by
  rw [WythoffCoarseningDatum.coe_maximalCone, show exampleDatum.WJ = ⊥ from rfl,
    aetGeneralizedChamber_bot]
  ext x
  simp [aetChamber, examplePhi]

/-- The maximal cone is a member. -/
theorem example_maximal_mem : exampleDatum.maximalCone ∈ exampleDatum.coarsenedCones :=
  exampleDatum.maximal_mem

/-- The apex is a face of the maximal cone.  Cone-intrinsically: any face of the half line
`{x | 0 ≤ x}` that contains `a • x + y = 0` with `a > 0`, `x, y ≥ 0` must have `x = 0`. -/
theorem example_apex_face : (⊥ : PointedCone ℝ ℝ).IsFaceOf exampleDatum.maximalCone where
  le := by
    intro x hx
    subst hx
    exact zero_mem _
  mem_of_smul_add_mem := by
    intro x y a hx hy ha hsum
    have hx0 : 0 ≤ x := by
      have h : x ∈ (exampleDatum.maximalCone : Set ℝ) := hx
      rw [example_maximalCone] at h
      exact h
    have hy0 : 0 ≤ y := by
      have h : y ∈ (exampleDatum.maximalCone : Set ℝ) := hy
      rw [example_maximalCone] at h
      exact h
    have hzero : a • x + y = 0 := by
      have h : a • x + y ∈ (⊥ : PointedCone ℝ ℝ) := hsum
      simpa using h
    have hx1 : x = 0 := by
      rw [smul_eq_mul] at hzero
      nlinarith
    simp [hx1]

/-- The apex is a member: O2 applied on the example. -/
theorem example_apex_mem : (⊥ : PointedCone ℝ ℝ) ∈ exampleDatum.coarsenedCones :=
  exampleDatum.mem_of_isFaceOf exampleDatum.maximal_mem example_apex_face

/-- A separating example: the ambient line is not a member.  A face of the half line `{x | 0 ≤ x}`
is a subcone of it, and `ℝ` is not. -/
theorem example_top_not_mem : (⊤ : PointedCone ℝ ℝ) ∉ exampleDatum.coarsenedCones := by
  rintro ⟨g, hg, hface⟩
  have h1 : (g : ℝ ≃ₗ[ℝ] ℝ) = 1 := Subgroup.mem_bot.mp hg
  have hx : (-1 : ℝ) ∈ (exampleDatum.maximalCone : Set ℝ) := by
    have hle : (-1 : ℝ) ∈ (exampleDatum.translate g : Set ℝ) :=
      hface.le (show (-1 : ℝ) ∈ (⊤ : PointedCone ℝ ℝ) from trivial)
    rwa [WythoffCoarseningDatum.coe_translate, h1,
      show ((1 : ℝ ≃ₗ[ℝ] ℝ) : ℝ → ℝ) = id from rfl, Set.image_id] at hle
  rw [example_maximalCone] at hx
  norm_num at hx

/-- The maximal-cone intersection law on the example: `W` is trivial. -/
theorem example_maximalConesMeetInFaces : exampleDatum.MaximalConesMeetInFaces := by
  have hsub : Subsingleton ↥exampleDatum.W :=
    ⟨fun a b => Subtype.ext (by
      rw [show a.1 = 1 from Subgroup.mem_bot.mp (show a.1 ∈ (⊥ : Subgroup (ℝ ≃ₗ[ℝ] ℝ)) from a.2),
        show b.1 = 1 from Subgroup.mem_bot.mp (show b.1 ∈ (⊥ : Subgroup (ℝ ≃ₗ[ℝ] ℝ)) from b.2)])⟩
  exact exampleDatum.maximalConesMeetInFaces_of_subsingleton

/-- The other non-vacuous case of the law, on the every-wall-irrelevant datum: no functional,
`W_irr = W = ⊤`. -/
def examplePhiEmpty : Empty → ℝ →ₗ[ℝ] ℝ := fun i => i.elim

/-- The datum with every wall irrelevant. -/
def exampleDatumTop : WythoffCoarseningDatum examplePhiEmpty (∅ : Finset Empty) where
  W := ⊤
  WJ := ⊤
  WJ_le := le_rfl
  active_nonneg := by intro i; exact i.elim
  convex := by
    intro x _ y _
    exact mem_aetGeneralizedChamber.mpr ⟨1, x + y, fun i => i.elim, rfl⟩
  irrelevant_flips := by intro j hj; exact absurd hj (by simp)

/-- The law holds there: with every wall irrelevant the family has one maximal cone modulo `W`. -/
theorem example_top_maximalConesMeetInFaces : exampleDatumTop.MaximalConesMeetInFaces :=
  exampleDatumTop.maximalConesMeetInFaces_of_WJ_eq_top rfl

end LeanCategories.Lattices.Valued

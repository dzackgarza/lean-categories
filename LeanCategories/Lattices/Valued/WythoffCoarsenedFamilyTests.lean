/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.WythoffCoarsenedFamily
public import Mathlib.Tactic

/-!
# Probes for #180, on the smallest inputs that decide them

Each declaration is a concrete instance that decides one clause of #180 on an input small enough to
read off the answer, so that none of the three obligations is discharged only by a vacuous
hypothesis.

* First datum (`probeDatum`): the rank-one chamber of `ℝ` — one functional, the identity; no
  irrelevant vertex; trivial reflection group. Here `𝒞_gen = {x | 0 ≤ x}` and the coarsened family
  is the family of faces of that half line.
  - `probe_maximalCone`, `probe_maximalCone_mem`: the maximal cone is a member.
  - `probe_zero_face`, `probe_zero_mem`: **O2 on a nontrivial face** — the apex is a face of the
    maximal cone, and gets into the family through `coarsenedFamily_faceClosed`, not by exhibiting
    a translate.
  - `probe_negative_not_mem`: **the separating example.** The opposite half line `{x | x ≤ 0}` is
    *not* a member, so the family is not the whole powerset and the maximal cone's face family is
    not saturated. (This is the wrong-model test: a weaker definition — "any subset of some
    translate", or a family that includes the irrelevant half — would accept it.)
  - `probe_maximalConesMeetInFaces`, `probe_inf_commonFace`: **O3** on two genuinely different
    members, through the trivial-group discharge of the geometric input.
* Second datum (`probeDatumTop`): no functional at all (`ι = Empty`), every vertex irrelevant
  (`W_irr = W = ⊤`). Here `𝒞_gen` is the whole space, so the geometric input O3 needs is
  discharged by `maximalConesMeetInFaces_of_WJ_eq_top`, the non-vacuous case of the discharge: the
  coarsened family has a single maximal cone modulo `W` because `𝒞_gen` is invariant under every
  linear equivalence.
  - `probe_top_maximalConesMeetInFaces`, `probe_top_inf_commonFace`: **O3** on that datum.
  - `probe_empty_mem`: the vacant member, documenting the caveat recorded at `coarsenedFamily`:
    the set-level face relation accepts `∅`, which is not a cone. It is a member here, and both
    clauses are proved for every member, so the cone-intrinsic version is unaffected.
-/

@[expose] public section

namespace LeanCategories.Lattices.Valued

/-! ## The rank-one chamber of `ℝ` -/

/-- The single simple-root functional of the rank-one probe: the identity of `ℝ`. -/
def probePhi : Unit → ℝ →ₗ[ℝ] ℝ := fun _ => LinearMap.id

/-- The AET datum of the rank-one probe: no irrelevant vertex, trivial reflection group. -/
def probeDatum : WythoffCoarseningDatum probePhi (∅ : Finset Unit) where
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

/-- The maximal cone of the rank-one probe is the closed half line `{x | 0 ≤ x}`. -/
theorem probe_maximalCone : probeDatum.maximalCone = {x : ℝ | 0 ≤ x} := by
  rw [WythoffCoarseningDatum.maximalCone, show probeDatum.WJ = ⊥ from rfl,
    aetGeneralizedChamber_bot]
  ext x
  simp [aetChamber, probePhi]

/-- The maximal cone is a member of its own coarsened family. -/
theorem probe_maximalCone_mem : probeDatum.maximalCone ∈ probeDatum.coarsenedFamily :=
  WythoffCoarseningDatum.maximalCone_mem probeDatum

/-- The apex is a face of the maximal cone: `{0}` satisfies the set-level face condition in the
half line `{x | 0 ≤ x}`. -/
theorem probe_zero_face : IsConeFace ({0} : Set ℝ) probeDatum.maximalCone := by
  rw [probe_maximalCone]
  refine ⟨?_, ?_⟩
  · intro x hx
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    subst hx0
    simp
  · intro x hx y hy hxy
    have hx0 : (0 : ℝ) ≤ x := by simpa using hx
    have hy0 : (0 : ℝ) ≤ y := by simpa using hy
    have hsum : x + y = 0 := by simpa using hxy
    have hx1 : x = 0 := by linarith
    have hy1 : y = 0 := by linarith
    rw [hx1, hy1]
    simp

/-- **O2 on the apex**: `{0}` is a member, obtained from the maximal cone by face closure. -/
theorem probe_zero_mem : ({0} : Set ℝ) ∈ probeDatum.coarsenedFamily :=
  WythoffCoarseningDatum.coarsenedFamily_faceClosed probeDatum probe_maximalCone_mem
    probe_zero_face

/-- **The separating example**: the opposite half line is not a member. -/
theorem probe_negative_not_mem : {x : ℝ | x ≤ 0} ∉ probeDatum.coarsenedFamily := by
  rw [WythoffCoarseningDatum.coarsenedFamily_of_W_eq_bot probeDatum (rfl : probeDatum.W = ⊥)]
  intro h
  have h1 : (-1 : ℝ) ∈ probeDatum.maximalCone := h.1 (by norm_num)
  rw [probe_maximalCone] at h1
  norm_num at h1

/-- **O3 on the rank-one probe**: the geometric input holds for the trivial reflection group. -/
theorem probe_maximalConesMeetInFaces : probeDatum.MaximalConesMeetInFaces := by
  have : Subsingleton ↥probeDatum.W :=
    ⟨fun a b => Subtype.ext (by
      have ha : a.1 = 1 := Subgroup.mem_bot.mp (show a.1 ∈ (⊥ : Subgroup (ℝ ≃ₗ[ℝ] ℝ)) from a.2)
      have hb : b.1 = 1 := Subgroup.mem_bot.mp (show b.1 ∈ (⊥ : Subgroup (ℝ ≃ₗ[ℝ] ℝ)) from b.2)
      rw [ha, hb])⟩
  exact WythoffCoarseningDatum.maximalConesMeetInFaces_of_subsingleton probeDatum

/-- **O3, universal pairwise intersection-as-common-face, on two different members**: the
intersection of the half line with its apex is a face of each. -/
theorem probe_inf_commonFace :
    IsConeFace (probeDatum.maximalCone ∩ ({0} : Set ℝ)) probeDatum.maximalCone ∧
      IsConeFace (probeDatum.maximalCone ∩ ({0} : Set ℝ)) ({0} : Set ℝ) :=
  WythoffCoarseningDatum.coarsenedFamily_inf_commonFace probeDatum
    probe_maximalConesMeetInFaces probe_maximalCone_mem probe_zero_mem

/-- The intersection of two members is again a member. -/
theorem probe_inf_mem :
    probeDatum.maximalCone ∩ ({0} : Set ℝ) ∈ probeDatum.coarsenedFamily :=
  WythoffCoarseningDatum.coarsenedFamily_inf_mem probeDatum probe_maximalConesMeetInFaces
    probe_maximalCone_mem probe_zero_mem

/-! ## The every-wall-irrelevant probe -/

/-- No simple-root functional at all. -/
def probePhiEmpty : Empty → ℝ →ₗ[ℝ] ℝ := fun i => i.elim

/-- The AET datum with every wall irrelevant: `W_irr = W = ⊤`. -/
def probeDatumTop : WythoffCoarseningDatum probePhiEmpty (∅ : Finset Empty) where
  W := ⊤
  WJ := ⊤
  WJ_le := le_rfl
  active_nonneg := by intro i; exact i.elim
  convex := by
    intro x _ y _
    exact mem_aetGeneralizedChamber.mpr ⟨1, x + y, fun i => i.elim, rfl⟩
  irrelevant_flips := by intro j hj; exact absurd hj (by simp)

/-- **The non-vacuous discharge of the geometric input of O3**: with every wall irrelevant the
maximal cone is invariant under every linear equivalence, so two translates of it coincide. -/
theorem probe_top_maximalConesMeetInFaces : probeDatumTop.MaximalConesMeetInFaces :=
  WythoffCoarseningDatum.maximalConesMeetInFaces_of_WJ_eq_top probeDatumTop rfl

/-- The vacant member: `∅` satisfies the set-level face relation vacuously. This is the caveat
recorded at `coarsenedFamily`, on the smallest input. -/
theorem probe_empty_mem : (∅ : Set ℝ) ∈ probeDatumTop.coarsenedFamily :=
  ⟨1, Subgroup.mem_top 1, by
    refine ⟨Set.empty_subset _, ?_⟩
    intro x _ y _ hxy
    exact absurd hxy (by simp)⟩

/-- **O3 on the every-wall-irrelevant datum**, with the vacant member as one of the two. -/
theorem probe_top_inf_commonFace :
    IsConeFace (probeDatumTop.maximalCone ∩ ∅) probeDatumTop.maximalCone :=
  (WythoffCoarseningDatum.coarsenedFamily_inf_commonFace probeDatumTop
    probe_top_maximalConesMeetInFaces (WythoffCoarseningDatum.maximalCone_mem probeDatumTop)
    probe_empty_mem).1

/-- The maximal cone of the every-wall-irrelevant probe is the whole space: with no functional the
chamber is `univ`, and so is the union of its translates. -/
theorem probe_top_maximalCone : probeDatumTop.maximalCone = Set.univ := by
  rw [WythoffCoarseningDatum.maximalCone, Set.eq_univ_iff_forall]
  intro x
  exact mem_aetGeneralizedChamber.mpr ⟨1, x, fun i => i.elim, rfl⟩

end LeanCategories.Lattices.Valued

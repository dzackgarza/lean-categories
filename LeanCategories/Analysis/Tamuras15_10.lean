/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Convex.Cone.Extension

@[expose] public section

/-!
# The corrected statement of `P-TAMURAS15-10`

Card `P-TAMURAS15-10` of the qualifying-exam corpus.  Source: TAMU real-analysis
qualifying exam, Spring 2015, problem 10, as transcribed in the new-qual-site
collection `SRC-TAMU-RA-SPRING-2015`.  Certificate: new-qual-site
`proofs/cards/Tamuras15_10.lean` at main `16c09abaa4`.

Setting: a real normed space `E`, a closed subspace `Y`, a second norm `n1` on `Y`
with `n1 y ≤ K * ‖y‖` and `‖y‖ ≤ K * n1 y` for a constant `K > 1`, and

  `S = {φ : E →L[ℝ] ℝ // (∀ y : Y, |φ y| ≤ n1 y) ∧ ‖φ‖ ≤ K}`.

Proved here: every element of `Y` is attained by a member of `S` (`exists_mem_S`,
the `x ∈ Y` case of the definiteness argument and claim (ii)); every `x ≠ 0` is
separated by a member of `S` (`exists_mem_S_ne_zero`, using the closed complement
case from `NormExtension.lean`, repeated here to keep the file self-contained), so
`‖x‖₂ = sup {|φ x| : φ ∈ S}` is definite (`norm₂_pos`); and the two-sided
comparison `norm₂_bound`, with `norm₂` also nonnegative, homogeneous and
subadditive.
-/

set_option linter.style.haveILetI false

namespace LeanCategories.Analysis.Tamuras15_10


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y : Submodule ℝ E}

/-- A second norm on a subspace `Y`, with its two comparison inequalities. -/
structure SecondNorm (K : ℝ) (Y : Submodule ℝ E) where
  n : Y → ℝ
  nonneg : ∀ y, 0 ≤ n y
  eq_zero : ∀ y, n y = 0 → y = 0
  smul : ∀ (c : ℝ) (y : Y), n (c • y) = |c| * n y
  add_le : ∀ y z, n (y + z) ≤ n y + n z
  le_norm : ∀ y, n y ≤ K * ‖y‖
  norm_le : ∀ y, ‖y‖ ≤ K * n y

/-- Closed-complement case: for `x ∉ Y` a functional of norm at most one vanishing on
`Y` with `φ x ≠ 0` (as in `NormExtension.lean`, repeated here to keep the file
self-contained). -/
theorem exists_dual_vanishing {Y : Submodule ℝ E} (hY : IsClosed (Y : Set E)) {x : E}
    (hx : x ∉ Y) : ∃ f : StrongDual ℝ E, f x ≠ 0 ∧ (∀ y ∈ Y, f y = 0) ∧ ‖f‖ ≤ 1 := by
  classical
  haveI := hY
  have hxq : (Submodule.Quotient.mk (p := Y) x : E ⧸ Y) ≠ 0 := by
    intro h
    exact hx ((Submodule.Quotient.mk_eq_zero Y).mp h)
  obtain ⟨g, hg1, hgx⟩ :=
    exists_dual_vector ℝ (Submodule.Quotient.mk (p := Y) x : E ⧸ Y) (by simpa using hxq)
  let q : E →L[ℝ] E ⧸ Y :=
    (Submodule.mkQ Y).mkContinuous 1 (fun z => by
      simpa [Submodule.mkQ_apply] using Submodule.Quotient.norm_mk_le Y z)
  refine ⟨g.comp q, ?_, ?_, ?_⟩
  · have hval : (g.comp q) x = g (Submodule.Quotient.mk (p := Y) x) := by simp [q]
    rw [hval, hgx]
    have hpos : (0 : ℝ) < ‖(Submodule.Quotient.mk (p := Y) x : E ⧸ Y)‖ := by
      rw [norm_pos_iff]; exact hxq
    intro hzero
    exact hpos.ne' (by exact_mod_cast hzero)
  · intro y hy
    have hy0 : (Submodule.Quotient.mk (p := Y) y : E ⧸ Y) = 0 :=
      (Submodule.Quotient.mk_eq_zero Y).mpr hy
    simp [ContinuousLinearMap.comp_apply, q, hy0]
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => ?_)
    calc ‖(g.comp q) z‖
        = ‖g (Submodule.Quotient.mk (p := Y) z)‖ := by simp [q]
      _ ≤ ‖g‖ * ‖(Submodule.Quotient.mk (p := Y) z : E ⧸ Y)‖ := g.le_opNorm _
      _ = ‖(Submodule.Quotient.mk (p := Y) z : E ⧸ Y)‖ := by rw [hg1, one_mul]
      _ ≤ ‖z‖ := Submodule.Quotient.norm_mk_le Y z
      _ = 1 * ‖z‖ := (one_mul _).symm

/-- The set `S` of functionals of the problem. -/
def S (N : SecondNorm (E := E) K Y) : Set (StrongDual ℝ E) :=
  {φ | (∀ y : Y, |φ y| ≤ N.n y) ∧ ‖φ‖ ≤ K}

variable {K : ℝ} {N : SecondNorm (E := E) K Y}

theorem n_zero : N.n (0 : Y) = 0 := by
  have h := N.smul 0 (0 : Y)
  simpa using h

theorem n_pos (y : Y) (hy : y ≠ 0) : 0 < N.n y :=
  lt_of_le_of_ne (N.nonneg y) (fun h => hy (N.eq_zero y h.symm))

theorem zero_mem_S (hK : 0 ≤ K) : (0 : StrongDual ℝ E) ∈ S N := by
  refine ⟨fun y => ?_, by simpa using hK⟩
  simp [N.nonneg y]

/-- Every element of `Y` is attained by a functional of `S`. -/
theorem exists_mem_S (hK : 1 < K) (y : Y) : ∃ φ ∈ S N, φ y = N.n y := by
  classical
  by_cases hy : y = 0
  · refine ⟨0, zero_mem_S (N := N) (le_trans zero_le_one (le_of_lt hK)), ?_⟩
    simp [hy, n_zero (N := N)]
  · let e : ℝ ≃ₗ[ℝ] ↥(ℝ ∙ y) := LinearEquiv.toSpanNonzeroSingleton ℝ Y y hy
    let l : ↥(ℝ ∙ y) →ₗ[ℝ] ℝ := (LinearMap.mul ℝ ℝ (N.n y)).comp e.symm.toLinearMap
    have h1 : e.symm ⟨y, Submodule.mem_span_singleton_self y⟩ = 1 := by
      apply e.injective
      simp [e]
    have hly : l ⟨y, Submodule.mem_span_singleton_self y⟩ = N.n y := by
      simp [l, h1]
    obtain ⟨g, hgy, hgle⟩ := exists_extension_of_le_sublinear
      (LinearPMap.mk (ℝ ∙ y) l) N.n
      (fun c hc z => by rw [N.smul c z, abs_of_pos hc])
      (fun z w => N.add_le z w)
      (by
        intro z
        obtain ⟨c, hc⟩ : ∃ c : ℝ, c • y = (z : Y) := Submodule.mem_span_singleton.mp z.2
        have hval : l z = c * N.n y := by
          have hz1 : e.symm z = c := by
            apply e.injective
            rw [LinearEquiv.apply_symm_apply]
            simp [e, hc]
          simp [l, hz1, mul_comm]
        change l z ≤ N.n (z : Y)
        rw [hval, ← hc, N.smul]
        exact mul_le_mul_of_nonneg_right (le_abs_self c) (N.nonneg y))
    have hgy' : g y = N.n y := by
      have h := hgy ⟨y, Submodule.mem_span_singleton_self y⟩
      rw [LinearPMap.mk_apply, hly] at h
      exact h
    have hg_abs : ∀ z : Y, |g z| ≤ N.n z := by
      intro z
      refine abs_le.mpr ⟨?_, hgle z⟩
      have h := hgle (-z)
      have hneg : N.n (-z) = N.n z := by
        have hs := N.smul (-1) z
        simpa using hs
      rw [map_neg, hneg] at h
      linarith
    let gc : Y →L[ℝ] ℝ := g.mkContinuous K (fun z => by
      rw [Real.norm_eq_abs]
      exact le_trans (hg_abs z) (N.le_norm z))
    have hgc : ‖gc‖ ≤ K := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) (fun z => ?_)
      exact le_trans (le_of_eq rfl) (by
        rw [Real.norm_eq_abs]
        exact le_trans (hg_abs z) (N.le_norm z))
    obtain ⟨F, hF, hFnorm⟩ := exists_extension_norm_eq Y gc
    have hFy : F y = N.n y := by
      rw [hF]
      show gc y = N.n y
      rw [LinearMap.mkContinuous_apply]
      exact hgy'
    exact ⟨F, ⟨fun z => by rw [hF z]; exact hg_abs z, by rw [hFnorm]; exact hgc⟩, hFy⟩

/-- The set whose supremum is the candidate second norm at `x`. -/
def vals (N : SecondNorm (E := E) K Y) (x : E) : Set ℝ :=
  {r : ℝ | ∃ φ ∈ S N, r = |φ x|}

theorem bddAbove_vals (_hK : 1 < K) (x : E) : BddAbove (vals N x) := by
  refine ⟨K * ‖x‖, ?_⟩
  rintro r ⟨φ, hφ, rfl⟩
  calc |φ x| ≤ ‖φ‖ * ‖x‖ := φ.le_opNorm x
    _ ≤ K * ‖x‖ := by
      refine mul_le_mul_of_nonneg_right hφ.2 (norm_nonneg x)

theorem zero_mem_vals (hK : 1 < K) (x : E) : (0 : ℝ) ∈ vals N x :=
  ⟨0, zero_mem_S (N := N) (le_trans zero_le_one (le_of_lt hK)), by simp⟩

/-- The candidate second norm of the problem: `sup {|φ x| : φ ∈ S}`. -/
noncomputable def norm₂ (N : SecondNorm (E := E) K Y) (x : E) : ℝ := sSup (vals N x)

theorem norm₂_nonneg (hK : 1 < K) (x : E) : 0 ≤ norm₂ N x :=
  le_csSup (bddAbove_vals (N := N) hK x) (zero_mem_vals (N := N) hK x)

theorem norm₂_le (hK : 1 < K) (x : E) : norm₂ N x ≤ K * ‖x‖ :=
  csSup_le ⟨0, zero_mem_vals (N := N) hK x⟩ (by
    rintro r ⟨φ, hφ, rfl⟩
    calc |φ x| ≤ ‖φ‖ * ‖x‖ := φ.le_opNorm x
      _ ≤ K * ‖x‖ := mul_le_mul_of_nonneg_right hφ.2 (norm_nonneg x))

theorem abs_le_norm₂ {hK : 1 < K} {x : E} {φ : StrongDual ℝ E} (hφ : φ ∈ S N) :
    |φ x| ≤ norm₂ N x :=
  le_csSup (bddAbove_vals (N := N) hK x) ⟨φ, hφ, rfl⟩

theorem norm₂_add_le (hK : 1 < K) (x y : E) :
    norm₂ N (x + y) ≤ norm₂ N x + norm₂ N y := by
  refine csSup_le ⟨0, zero_mem_vals (N := N) hK (x + y)⟩ (by
    rintro r ⟨φ, hφ, rfl⟩
    calc |φ (x + y)| = |φ x + φ y| := by rw [map_add]
      _ ≤ |φ x| + |φ y| := by
            have h1 : -(φ x) ≤ |φ x| := neg_le_abs (φ x)
            have h2 : φ x ≤ |φ x| := le_abs_self (φ x)
            have h3 : -(φ y) ≤ |φ y| := neg_le_abs (φ y)
            have h4 : φ y ≤ |φ y| := le_abs_self (φ y)
            exact abs_le.mpr ⟨by linarith, by linarith⟩
      _ ≤ norm₂ N x + norm₂ N y := add_le_add (abs_le_norm₂ (N := N) (hK := hK) hφ) (abs_le_norm₂ (N := N) (hK := hK) hφ))

theorem norm₂_smul_le (hK : 1 < K) (c : ℝ) (x : E) :
    norm₂ N (c • x) ≤ |c| * norm₂ N x := by
  refine csSup_le ⟨0, zero_mem_vals (N := N) hK (c • x)⟩ (by
    rintro r ⟨φ, hφ, rfl⟩
    rw [ContinuousLinearMap.map_smul, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le_norm₂ (N := N) (hK := hK) hφ) (abs_nonneg c))

theorem zero_mem_S' (hK : 1 < K) : (0 : StrongDual ℝ E) ∈ S N :=
  zero_mem_S (N := N) (le_trans zero_le_one (le_of_lt hK))

theorem norm₂_zero (hK : 1 < K) : norm₂ N (0 : E) = 0 := by
  have hb := bddAbove_vals (N := N) hK (0 : E)
  have hle : norm₂ N (0 : E) ≤ 0 := by
    refine csSup_le ⟨0, zero_mem_vals (N := N) hK 0⟩ (by
      rintro r ⟨φ, hφ, rfl⟩
      simp)
  exact le_antisymm hle (norm₂_nonneg (N := N) hK 0)

theorem exists_mem_S_ne_zero (hYc : IsClosed (Y : Set E)) (hK : 1 < K) {x : E} (hx : x ≠ 0) :
    ∃ φ ∈ S N, φ x ≠ 0 := by
  by_cases hxY : x ∈ Y
  · obtain ⟨φ, hφS, hφx⟩ := exists_mem_S (N := N) hK ⟨x, hxY⟩
    refine ⟨φ, hφS, ?_⟩
    rw [hφx]
    exact ne_of_gt (n_pos (N := N) ⟨x, hxY⟩ (fun h => hx (by simpa using h)))
  · obtain ⟨f, hfx, hfY, hfnorm⟩ := exists_dual_vanishing hYc hxY
    refine ⟨f, ⟨fun y => ?_, by linarith⟩, hfx⟩
    rw [hfY (y : E) y.2, abs_zero]
    exact N.nonneg y

theorem norm₂_pos (hYc : IsClosed (Y : Set E)) (hK : 1 < K) {x : E} (hx : x ≠ 0) :
    0 < norm₂ N x := by
  obtain ⟨φ, hφS, hφx⟩ := exists_mem_S_ne_zero (N := N) hYc hK hx
  have hpos : 0 < |φ x| := abs_pos.mpr hφx
  exact lt_of_lt_of_le hpos (abs_le_norm₂ (N := N) (hK := hK) hφS)

theorem norm₂_eq_zero_iff (hYc : IsClosed (Y : Set E)) (hK : 1 < K) {x : E} :
    norm₂ N x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (norm₂_pos (N := N) hYc hK hx).ne' h
  · intro h
    subst h
    exact norm₂_zero (N := N) hK

/-- Claim (ii): on `Y` the candidate norm agrees with `n`. -/
theorem norm₂_of_mem (hK : 1 < K) (y : Y) : norm₂ N (y : E) = N.n y := by
  refine le_antisymm ?_ ?_
  · refine csSup_le ⟨0, zero_mem_vals (N := N) hK (y : E)⟩ (by
      rintro r ⟨φ, hφ, rfl⟩
      exact hφ.1 y)
  · have hmem : N.n y ∈ vals N (y : E) := by
      obtain ⟨φ, hφS, hφy⟩ := exists_mem_S (N := N) hK y
      exact ⟨φ, hφS, by rw [hφy, abs_of_nonneg (N.nonneg y)]⟩
    exact le_csSup (bddAbove_vals (N := N) hK (y : E)) hmem

/-- Claim (iii), lower bound: the candidate norm dominates `‖·‖ / K`. -/
theorem le_norm₂ (hK : 1 < K) (x : E) : ‖x‖ ≤ K * norm₂ N x := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    simp [norm₂_zero (N := N) hK]
  · obtain ⟨g, hg1, hgx⟩ := exists_dual_vector ℝ x (by simpa using hx)
    have hKpos : 0 < K := by linarith
    have hinv : K⁻¹ ≤ K := by
      have h1 : K⁻¹ * K = 1 := inv_mul_cancel₀ (ne_of_gt hKpos)
      nlinarith [inv_pos.mpr hKpos]
    set φ : StrongDual ℝ E := (K⁻¹ : ℝ) • g with hφdef
    have hφapply : ∀ z : E, φ z = K⁻¹ * g z := by
      intro z
      simp [hφdef]
    have hφnorm : ‖φ‖ ≤ K := by
      have hval : ‖φ‖ = K⁻¹ := by
        rw [hφdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hKpos), hg1, mul_one]
      rw [hval]
      exact hinv
    have hφS : φ ∈ S N := by
      refine ⟨fun y => ?_, hφnorm⟩
      have hbound : |φ (y : E)| = K⁻¹ * |g (y : E)| := by
        rw [hφapply, abs_mul, abs_of_pos (inv_pos.mpr hKpos)]
      rw [hbound]
      have hgy : |g (y : E)| ≤ ‖y‖ := by
        calc |g (y : E)| = ‖g (y : E)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖g‖ * ‖(y : E)‖ := g.le_opNorm _
          _ = ‖(y : E)‖ := by rw [hg1, one_mul]
          _ = ‖y‖ := rfl
      refine le_trans (mul_le_mul_of_nonneg_left hgy (le_of_lt (inv_pos.mpr hKpos))) ?_
      have h1 : K⁻¹ * ‖y‖ ≤ K⁻¹ * (K * N.n y) :=
        mul_le_mul_of_nonneg_left (N.norm_le y) (le_of_lt (inv_pos.mpr hKpos))
      have h2 : K⁻¹ * (K * N.n y) = N.n y := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hKpos), one_mul]
      linarith
    have hstep : K⁻¹ * (‖x‖ : ℝ) ≤ norm₂ N x := by
      calc K⁻¹ * (‖x‖ : ℝ) = φ x := by simp [hφapply x, hgx]
        _ ≤ |φ x| := le_abs_self _
        _ ≤ norm₂ N x := abs_le_norm₂ (N := N) (hK := hK) (x := x) hφS
    calc (‖x‖ : ℝ) = K * (K⁻¹ * (‖x‖ : ℝ)) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hKpos), one_mul]
      _ ≤ K * norm₂ N x := mul_le_mul_of_nonneg_left hstep (le_of_lt hKpos)

theorem norm₂_smul (hK : 1 < K) (c : ℝ) (x : E) :
    norm₂ N (c • x) = |c| * norm₂ N x := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    simp [norm₂_zero (N := N) hK]
  · refine le_antisymm (norm₂_smul_le (N := N) hK c x) ?_
    have hcne : c ≠ 0 := hc
    have habs : (0 : ℝ) < |c| := abs_pos.mpr hcne
    have h1 : norm₂ N (c⁻¹ • (c • x)) ≤ |c⁻¹| * norm₂ N (c • x) :=
      norm₂_smul_le (N := N) hK c⁻¹ (c • x)
    rw [smul_smul, inv_mul_cancel₀ hcne, one_smul] at h1
    have h2 : |c⁻¹| = |c|⁻¹ := abs_inv c
    rw [h2] at h1
    have h3 : |c| * norm₂ N x ≤ |c| * (|c|⁻¹ * norm₂ N (c • x)) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt habs)
    have h4 : |c| * (|c|⁻¹ * norm₂ N (c • x)) = norm₂ N (c • x) := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt habs), one_mul]
    linarith

theorem inv_norm_le_norm₂ (hK : 1 < K) (x : E) :
    K⁻¹ * (‖x‖ : ℝ) ≤ norm₂ N x := by
  have hKpos : 0 < K := by linarith
  have h := le_norm₂ (N := N) hK x
  calc K⁻¹ * (‖x‖ : ℝ) ≤ K⁻¹ * (K * norm₂ N x) :=
        mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hKpos))
    _ = norm₂ N x := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hKpos), one_mul]

/-- The corrected card statement: `norm₂` is a norm on `E`, agrees with `n` on `Y`, and
is equivalent to `‖·‖` with the two constants of the problem. -/
theorem corrected_statement (hYc : IsClosed (Y : Set E)) (hK : 1 < K) :
    (∀ x, 0 ≤ norm₂ N x) ∧
    (∀ x, norm₂ N x = 0 ↔ x = 0) ∧
    (∀ (c : ℝ) (x : E), norm₂ N (c • x) = |c| * norm₂ N x) ∧
    (∀ x y, norm₂ N (x + y) ≤ norm₂ N x + norm₂ N y) ∧
    (∀ y : Y, norm₂ N (y : E) = N.n y) ∧
    (∀ x, K⁻¹ * (‖x‖ : ℝ) ≤ norm₂ N x ∧ norm₂ N x ≤ K * ‖x‖) :=
  ⟨fun x => norm₂_nonneg (N := N) hK x,
   fun _x => norm₂_eq_zero_iff (N := N) hYc hK,
   fun c x => norm₂_smul (N := N) hK c x,
   fun x y => norm₂_add_le (N := N) hK x y,
   fun y => norm₂_of_mem (N := N) hK y,
   fun x => ⟨inv_norm_le_norm₂ (N := N) hK x, norm₂_le (N := N) hK x⟩⟩

end LeanCategories.Analysis.Tamuras15_10

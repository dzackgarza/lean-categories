/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Algebra.Module.Basic

@[expose] public section

/-!
# The negative cone of the standard Lorentzian form

On `ℝ^{n,1} = Fin (n+1) → ℝ` with `lorentz x = -x₀² + ∑_{i≠0} xᵢ²` (Vinberg's `E^{n,1}`), the
negative cone `V = {x : lorentz x < 0}` is the disjoint union of the two open convex sheets
`V₊ = V ∩ {x₀ > 0}` and `V₋ = V ∩ {x₀ < 0}` (`negativeCone_two_components`). The key step is the
reverse Cauchy–Schwarz inequality `lorentzPair_neg_of_mem_upper`.

Provenance: migrated from `dzackgarza/research`,
`computations/scripts/sterk-enriques-cusps/lean/Atoms.lean` (sections `LorentzCone`,
`LorentzConvexity`; Sterk graph nodes Lo1, Lo10), unchanged in content.

LC-12. *Needed*: the two-sheet structure of the negative cone of a real quadratic form of
signature `(n, 1)`. *Searched*: the formalization corpus and Mathlib for Lorentz / light / time
cones and reverse Cauchy–Schwarz; nothing. *Did instead*: the statement for the standard
coordinate form only. *Optimal*: the statement for any `Q : QuadraticForm ℝ V` of negative index
one, obtained from this one by transport along Sylvester's normal form
(`QuadraticForm.equivalent_signType_weighted_sum_squared`); isometries carry negative cones to
negative cones. *Tracked*: TODO(LC-12) below and COMPLAINTS ("Lorentzian cone, coordinate-free").
-/

namespace LeanCategories.LorentzCone

/-- **Lo1, Lo10.**  The standard Lorentzian form on `Fin (n+1) → ℝ`: minus the
square of the zeroth coordinate plus the squares of the rest.  This is Vinberg's
`E^{n,1}`, the form of negative inertial index one his §3 works in. -/
def lorentz {n : ℕ} (x : Fin (n + 1) → ℝ) : ℝ :=
  -(x 0) ^ 2 + ∑ i ∈ Finset.univ.erase 0, (x i) ^ 2

/-- **Lo1.**  The negative cone `V = {x : (x,x) < 0}`. -/
def negativeCone (n : ℕ) : Set (Fin (n + 1) → ℝ) := {x | lorentz x < 0}

/-- The upper sheet `V₊`. -/
def negativeCone.upper (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | lorentz x < 0 ∧ 0 < x 0}

/-- The lower sheet `V₋`. -/
def negativeCone.lower (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | lorentz x < 0 ∧ x 0 < 0}

theorem lorentz_continuous {n : ℕ} : Continuous (lorentz (n := n)) := by
  unfold lorentz
  fun_prop

/-- On the negative cone the zeroth coordinate never vanishes: if it did, the
form would be a sum of squares there. -/
theorem ne_zero_of_mem_negativeCone {n : ℕ} {x : Fin (n + 1) → ℝ}
    (hx : x ∈ negativeCone n) : x 0 ≠ 0 := by
  intro h0
  have hsum : 0 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), (x i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hval : lorentz x = ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), (x i) ^ 2 := by
    unfold lorentz; rw [h0]; ring
  have hlt : lorentz x < 0 := hx
  rw [hval] at hlt
  exact absurd hlt (not_lt.mpr hsum)

/-- **Lo10, the separation half.**  The two sheets are disjoint, open, and cover
the cone, so the cone is disconnected by the sign of the zeroth coordinate.

The remaining half of Lo10 — that each sheet is *connected*, so that there are
exactly two components — is the convexity of a Lorentzian half-cone and is not
proved here. -/
theorem negativeCone_eq_union (n : ℕ) :
    negativeCone n = negativeCone.upper n ∪ negativeCone.lower n := by
  ext x
  constructor
  · intro hx
    rcases lt_or_gt_of_ne (ne_zero_of_mem_negativeCone hx) with h | h
    · exact Or.inr ⟨hx, h⟩
    · exact Or.inl ⟨hx, h⟩
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx

theorem negativeCone.upper_disjoint_lower (n : ℕ) :
    Disjoint (negativeCone.upper n) (negativeCone.lower n) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, hpos⟩ ⟨-, hneg⟩
  exact absurd hpos (not_lt.mpr hneg.le)

theorem negativeCone.isOpen_upper (n : ℕ) : IsOpen (negativeCone.upper n) := by
  have h1 : IsOpen {x : Fin (n + 1) → ℝ | lorentz x < 0} :=
    isOpen_lt lorentz_continuous continuous_const
  have h2 : IsOpen {x : Fin (n + 1) → ℝ | 0 < x 0} :=
    isOpen_lt continuous_const ((continuous_apply 0))
  exact h1.inter h2

theorem negativeCone.isOpen_lower (n : ℕ) : IsOpen (negativeCone.lower n) := by
  have h1 : IsOpen {x : Fin (n + 1) → ℝ | lorentz x < 0} :=
    isOpen_lt lorentz_continuous continuous_const
  have h2 : IsOpen {x : Fin (n + 1) → ℝ | x 0 < 0} :=
    isOpen_lt ((continuous_apply 0)) continuous_const
  exact h1.inter h2

variable {n : ℕ}

/-- The Lorentzian pairing whose diagonal is `lorentz`. -/
def lorentzPair (x y : Fin (n + 1) → ℝ) : ℝ :=
  -(x 0 * y 0) + ∑ i ∈ Finset.univ.erase 0, x i * y i

theorem lorentz_eq_lorentzPair_self (x : Fin (n + 1) → ℝ) : lorentz x = lorentzPair x x := by
  unfold lorentz lorentzPair
  simp only [sq]

/-- The form expands on a linear combination through the pairing. -/
theorem lorentz_smul_add (a b : ℝ) (x y : Fin (n + 1) → ℝ) :
    lorentz (a • x + b • y)
      = a ^ 2 * lorentz x + b ^ 2 * lorentz y + 2 * a * b * lorentzPair x y := by
  unfold lorentz lorentzPair
  have hpt : ∀ i : Fin (n + 1),
      ((a • x + b • y) i) ^ 2
        = a ^ 2 * (x i) ^ 2 + b ^ 2 * (y i) ^ 2 + 2 * a * b * (x i * y i) := by
    intro i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The spatial part of a vector on the cone is shorter than its time part. -/
theorem sum_sq_lt_sq_of_mem_negativeCone {x : Fin (n + 1) → ℝ} (hx : x ∈ negativeCone n) :
    ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), (x i) ^ 2 < (x 0) ^ 2 := by
  have h : lorentz x < 0 := hx
  unfold lorentz at h
  linarith

/-- **Lo10.**  The pairing of two future-directed vectors of the cone is
negative: the reverse Cauchy–Schwarz inequality for a form of index one. -/
theorem lorentzPair_neg_of_mem_upper {x y : Fin (n + 1) → ℝ}
    (hx : x ∈ negativeCone.upper n) (hy : y ∈ negativeCone.upper n) :
    lorentzPair x y < 0 := by
  obtain ⟨hxc, hx0⟩ := hx
  obtain ⟨hyc, hy0⟩ := hy
  set S := Finset.univ.erase (0 : Fin (n + 1)) with hS
  have hxs : ∑ i ∈ S, (x i) ^ 2 < (x 0) ^ 2 := sum_sq_lt_sq_of_mem_negativeCone hxc
  have hys : ∑ i ∈ S, (y i) ^ 2 < (y 0) ^ 2 := sum_sq_lt_sq_of_mem_negativeCone hyc
  have hxnn : (0:ℝ) ≤ ∑ i ∈ S, (x i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hynn : (0:ℝ) ≤ ∑ i ∈ S, (y i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs : (∑ i ∈ S, x i * y i) ^ 2 ≤ (∑ i ∈ S, (x i) ^ 2) * ∑ i ∈ S, (y i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq S x y
  have hprod : (∑ i ∈ S, (x i) ^ 2) * (∑ i ∈ S, (y i) ^ 2) < (x 0 * y 0) ^ 2 := by
    have h1 : (∑ i ∈ S, (x i) ^ 2) * (∑ i ∈ S, (y i) ^ 2) ≤ (x 0) ^ 2 * ∑ i ∈ S, (y i) ^ 2 :=
      mul_le_mul_of_nonneg_right hxs.le hynn
    have h2 : (x 0) ^ 2 * (∑ i ∈ S, (y i) ^ 2) < (x 0) ^ 2 * (y 0) ^ 2 := by
      have hx0sq : (0:ℝ) < (x 0) ^ 2 := by positivity
      exact mul_lt_mul_of_pos_left hys hx0sq
    calc (∑ i ∈ S, (x i) ^ 2) * (∑ i ∈ S, (y i) ^ 2) ≤ (x 0) ^ 2 * ∑ i ∈ S, (y i) ^ 2 := h1
      _ < (x 0) ^ 2 * (y 0) ^ 2 := h2
      _ = (x 0 * y 0) ^ 2 := by ring
  have hsq : (∑ i ∈ S, x i * y i) ^ 2 < (x 0 * y 0) ^ 2 := lt_of_le_of_lt hcs hprod
  have hpos : (0:ℝ) < x 0 * y 0 := mul_pos hx0 hy0
  have habs : ∑ i ∈ S, x i * y i < x 0 * y 0 := by
    nlinarith [hsq, hpos]
  unfold lorentzPair
  linarith

/-- **Lo10.**  The upper sheet is convex, hence connected. -/
theorem convex_upper (n : ℕ) : Convex ℝ (negativeCone.upper n) := by
  intro x hx y hy a b ha hb hab
  have hpair : lorentzPair x y < 0 := lorentzPair_neg_of_mem_upper hx hy
  obtain ⟨hxc, hx0⟩ := hx
  obtain ⟨hyc, hy0⟩ := hy
  have hxl : lorentz x < 0 := hxc
  have hyl : lorentz y < 0 := hyc
  constructor
  · change lorentz (a • x + b • y) < 0
    rw [lorentz_smul_add]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; norm_num; exact hyl
    · rcases eq_or_lt_of_le hb with rfl | hb'
      · have ha1 : a = 1 := by linarith
        subst ha1; norm_num; exact hxl
      · have t1 : a ^ 2 * lorentz x < 0 := mul_neg_of_pos_of_neg (by positivity) hxl
        have t2 : b ^ 2 * lorentz y < 0 := mul_neg_of_pos_of_neg (by positivity) hyl
        have t3 : 2 * a * b * lorentzPair x y < 0 :=
          mul_neg_of_pos_of_neg (by positivity) hpair
        linarith
  · change 0 < (a • x + b • y) 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; simpa using hy0
    · have u1 : 0 < a * x 0 := mul_pos ha' hx0
      have u2 : 0 ≤ b * y 0 := mul_nonneg hb hy0.le
      linarith

/-- The form is invariant under negation. -/
theorem lorentz_neg (z : Fin (n + 1) → ℝ) : lorentz (-z) = lorentz z := by
  unfold lorentz
  have h0 : ((-z) 0) ^ 2 = (z 0) ^ 2 := by
    simp only [Pi.neg_apply]; ring
  have hi : ∀ i : Fin (n + 1), ((-z) i) ^ 2 = (z i) ^ 2 := by
    intro i; simp only [Pi.neg_apply]; ring
  rw [h0, Finset.sum_congr rfl (fun i _ => hi i)]

/-- **Lo10.**  The lower sheet is convex too, being the image of the upper under
negation. -/
theorem convex_lower (n : ℕ) : Convex ℝ (negativeCone.lower n) := by
  intro x hx y hy a b ha hb hab
  have hx' : -x ∈ negativeCone.upper n := by
    obtain ⟨hxc, hx0⟩ := hx
    refine ⟨?_, ?_⟩
    · exact (lorentz_neg x).trans_lt hxc
    · simpa using hx0
  have hy' : -y ∈ negativeCone.upper n := by
    obtain ⟨hyc, hy0⟩ := hy
    refine ⟨?_, ?_⟩
    · exact (lorentz_neg y).trans_lt hyc
    · simpa using hy0
  have hcomb := convex_upper n hx' hy' ha hb hab
  obtain ⟨hc, h0⟩ := hcomb
  refine ⟨?_, ?_⟩
  · change lorentz (a • x + b • y) < 0
    have heq : a • (-x) + b • (-y) = -(a • x + b • y) := by
      ext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring
    rw [heq, lorentz_neg] at hc
    exact hc
  · change (a • x + b • y) 0 < 0
    have heq : (a • (-x) + b • (-y)) 0 = -((a • x + b • y) 0) := by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring
    rw [heq] at h0; linarith

/-- **Lo10, complete.**  The negative cone of the standard form of index one has
exactly two connected components: the two sheets, each convex hence connected,
disjoint, open, and covering the cone. -/
theorem negativeCone_two_components (n : ℕ) :
    IsPreconnected (negativeCone.upper n) ∧ IsPreconnected (negativeCone.lower n) ∧
      negativeCone n = negativeCone.upper n ∪ negativeCone.lower n ∧
      Disjoint (negativeCone.upper n) (negativeCone.lower n) ∧
      IsOpen (negativeCone.upper n) ∧ IsOpen (negativeCone.lower n) :=
  ⟨(convex_upper n).isPreconnected, (convex_lower n).isPreconnected,
    negativeCone_eq_union n, negativeCone.upper_disjoint_lower n,
    negativeCone.isOpen_upper n, negativeCone.isOpen_lower n⟩

-- TODO(LC-12): state `negativeCone_two_components` for a real quadratic form of negative index
-- one, by transport along Sylvester's normal form.

end LeanCategories.LorentzCone

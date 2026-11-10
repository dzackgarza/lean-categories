/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import LeanCategories.Topology.LorentzCone

/-!
# The positive cone of a real quadratic form of signature `(1, n)`

For a real quadratic form `Q` on a finite-dimensional real vector space `V` of signature
`(1, n)` — `sigPos Q = 1` — the positivity set `{x | 0 < Q x}` is the *positive cone*, with
two sheets: the set is the disjoint union of the two convex sets on which a fixed positive vector
`t` pairs positively (`positiveCone.upper`) and negatively (`positiveCone.lower`). Isometries of `Q`
permute the two sheets, so the stabilizer of a sheet (`positiveConeStabilizer`) has index at most
two in the orthogonal group: this is `O⁺(V, Q)`.

Everything here is proved from the single spectral hypothesis `sigPos Q = 1` and the choice of one
positive vector `t`; no diagonalization and no continuity is used.

## The mathematics

Let `Q` have signature `(1, n)`, i.e. `sigPos Q = 1`, and let `Q t > 0`. Then no two-dimensional
subspace is positive definite, which gives the *key inequality* `Q x * Q t ≤ b(x, t)²`
(`mul_self_le_formPairing_sq`): if it failed, the Gram matrix of `(t, x)` would be positive
definite (its determinant is positive and `Q t > 0`), and `le_sigPos_of_posDef` would put a
two-dimensional positive definite subspace inside a form of `sigPos` one. Projecting a vector off
`t` along `b(·, t)` turns it into a negative value of `Q`, and the key inequality is exactly the
reverse Cauchy–Schwarz inequality on `t^⊥` (`formPairing_spatialPart_sq_le`). Two points of the
cone pair positively exactly when they lie on the same side of `t^⊥`
(`formPairing_pos_of_mem_upper`, `formPairing_neg_of_mem_upper_lower`), which makes the two sides
convex and makes an isometry either fix both or exchange them.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 27: the
  positive cone of a Lorentzian lattice, its two sheets, and `O⁺` as the stabilizer of one.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Izv. Akad.
  Nauk SSSR Ser. Mat. 43 (1979), §1: `O(M)` and its index-two subgroup for K3 period lattices.
* J. G. Ratcliffe, *Foundations of Hyperbolic Manifolds*, 2nd ed., §3.1: the two-sheeted
  hyperboloid of a Lorentzian form and the reverse Cauchy–Schwarz inequality.
-/

@[expose] public section

open QuadraticMap

namespace LeanCategories.Lattices.Valued

universe u

/-- `2` is invertible in `ℝ`. Mathlib states the associated pairing of a quadratic form
through `⅟2` and does not register this instance, so the pairing below cannot be written. -/
noncomputable instance instInvertibleTwoReal : Invertible (2 : ℝ) :=
  invertibleOfNonzero (by norm_num)

section Pairing

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- The bilinear pairing `b(x, y) = ½(Q (x + y) - Q x - Q y)` associated to a quadratic form. It is
symmetric over `ℝ`, and `formPairing_self` recovers `Q` from it. -/
noncomputable def formPairing (Q : QuadraticForm ℝ V) (x y : V) : ℝ := (associated Q) x y

/-- The pairing of a vector with itself is its value under the form. -/
theorem formPairing_self (Q : QuadraticForm ℝ V) (x : V) : formPairing Q x x = Q x := by
  simpa [formPairing, QuadraticMap.coe_associatedHom] using
    QuadraticMap.associated_eq_self_apply (S := ℝ) (Q := Q) x

/-- The associated pairing is symmetric over `ℝ`. -/
theorem formPairing_comm (Q : QuadraticForm ℝ V) (x y : V) :
    formPairing Q x y = formPairing Q y x :=
  (QuadraticForm.associated_isSymm (S := ℝ) Q).eq x y

theorem formPairing_add_left (Q : QuadraticForm ℝ V) (x y z : V) :
    formPairing Q (x + y) z = formPairing Q x z + formPairing Q y z := by
  simp [formPairing]

theorem formPairing_smul_left (Q : QuadraticForm ℝ V) (a : ℝ) (x z : V) :
    formPairing Q (a • x) z = a * formPairing Q x z := by
  simp [formPairing, smul_eq_mul]

theorem formPairing_sub_left (Q : QuadraticForm ℝ V) (x y z : V) :
    formPairing Q (x - y) z = formPairing Q x z - formPairing Q y z := by
  simp [formPairing]

theorem formPairing_add_right (Q : QuadraticForm ℝ V) (x y z : V) :
    formPairing Q x (y + z) = formPairing Q x y + formPairing Q x z := by
  rw [formPairing_comm Q x (y + z), formPairing_add_left, formPairing_comm Q y x,
    formPairing_comm Q z x]

theorem formPairing_smul_right (Q : QuadraticForm ℝ V) (a : ℝ) (x z : V) :
    formPairing Q x (a • z) = a * formPairing Q x z := by
  rw [formPairing_comm Q x (a • z), formPairing_smul_left, formPairing_comm Q z x]

theorem formPairing_sub_right (Q : QuadraticForm ℝ V) (x y z : V) :
    formPairing Q x (y - z) = formPairing Q x y - formPairing Q x z := by
  rw [formPairing_comm Q x (y - z), formPairing_sub_left, formPairing_comm Q y x,
    formPairing_comm Q z x]

theorem formPairing_neg_left (Q : QuadraticForm ℝ V) (x y : V) :
    formPairing Q (-x) y = -formPairing Q x y := by
  rw [show -x = (-1 : ℝ) • x by simp, formPairing_smul_left]
  ring

theorem formPairing_neg_right (Q : QuadraticForm ℝ V) (x y : V) :
    formPairing Q x (-y) = -formPairing Q x y := by
  rw [show -y = (-1 : ℝ) • y by simp, formPairing_smul_right]
  ring

/-- The form evaluated on a linear combination, in terms of the pairing: the quadratic expansion
that every completed-square argument below uses. -/
theorem quadratic_expand (Q : QuadraticForm ℝ V) (a b : ℝ) (x y : V) :
    Q (a • x + b • y) = a ^ 2 * Q x + 2 * a * b * formPairing Q x y + b ^ 2 * Q y := by
  rw [← formPairing_self Q (a • x + b • y)]
  simp only [formPairing_add_left, formPairing_add_right, formPairing_smul_left,
    formPairing_smul_right, formPairing_comm Q y x]
  rw [formPairing_self, formPairing_self]
  ring

end Pairing

section Lorentzian

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {Q : QuadraticForm ℝ V}

/-- **The key inequality of a form of signature `(1, n)`.** For a positive vector `t`, no vector
`x` has `Q x * Q t > b(x, t)²`: that inequality would make `(t, x)` a positive definite plane,
which a form with `sigPos = 1` does not have. -/
theorem mul_self_le_formPairing_sq (hpos : sigPos Q = 1) {t : V} (ht : 0 < Q t) (x : V) :
    Q x * Q t ≤ formPairing Q x t ^ 2 := by
  by_contra hcon
  have hdet : formPairing Q x t ^ 2 < Q x * Q t := not_le.mp hcon
  have hPD : (Q.restrict (Submodule.span ℝ {t, x})).PosDef := by
    intro v hv
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp v.2
    rw [QuadraticMap.restrict_apply, ← hab, quadratic_expand, formPairing_comm Q t x]
    have hv' : a • t + b • x ≠ 0 := by
      intro hzero
      refine hv (Subtype.ext ?_)
      change (v : V) = 0
      rw [← hab, hzero]
    rcases eq_or_ne b 0 with hb0 | hb
    · subst hb0
      have ha : a ≠ 0 := by
        intro ha
        exact hv' (by rw [ha]; simp)
      nlinarith [sq_pos_of_ne_zero ha, ht]
    · nlinarith [sq_nonneg (a * Q t + b * formPairing Q x t), sq_pos_of_ne_zero hb, ht,
        mul_pos ht (sub_pos.mpr hdet)]
  have hdim : Module.finrank ℝ (Submodule.span ℝ {t, x}) ≤ 1 :=
    (le_sigPos_of_posDef (Q := Q) hPD).trans hpos.le
  have htne : t ≠ 0 := by
    intro h
    rw [h] at ht
    simp at ht
  have hsingle : Module.finrank ℝ (Submodule.span ℝ {t}) = 1 := by
    rw [finrank_span_singleton]
    simpa using htne
  have hspan : Submodule.span ℝ {t} = Submodule.span ℝ {t, x} := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · exact Submodule.span_mono
        (Set.singleton_subset_iff.mpr (Set.mem_insert_iff.mpr (Or.inl rfl)))
    · rw [hsingle]
      exact hdim
  have hx : x ∈ Submodule.span ℝ {t} := by
    rw [hspan]
    exact Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  have hQx : Q x = c ^ 2 * Q t := by
    rw [← hc, QuadraticMap.map_smul, smul_eq_mul]
    ring
  have hB : formPairing Q x t = c * Q t := by
    rw [← hc, formPairing_smul_left, formPairing_self]
  rw [hQx, hB] at hdet
  nlinarith [hdet, ht]

end Lorentzian

section Cone

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {Q : QuadraticForm ℝ V}

/-- The **positive cone** of a real quadratic form: the vectors of positive value. -/
def positiveCone (Q : QuadraticForm ℝ V) : Set V := {x | 0 < Q x}

/-- The sheet of the positive cone on which a positive vector `t` pairs positively. -/
def positiveCone.upper (Q : QuadraticForm ℝ V) (t : V) : Set V :=
  {x | 0 < Q x ∧ 0 < formPairing Q x t}

/-- The other sheet: the one on which a positive vector `t` pairs negatively. -/
def positiveCone.lower (Q : QuadraticForm ℝ V) (t : V) : Set V :=
  {x | 0 < Q x ∧ formPairing Q x t < 0}

/-- The projection of `x` off the line `ℝ t` along the pairing with `t`. -/
noncomputable def spatialPart (Q : QuadraticForm ℝ V) (t x : V) : V :=
  x - (formPairing Q x t / Q t) • t

omit [FiniteDimensional ℝ V] in
/-- The projection is orthogonal to `t`. -/
theorem formPairing_spatialPart_right (Q : QuadraticForm ℝ V) {t : V} (ht : Q t ≠ 0) (x : V) :
    formPairing Q (spatialPart Q t x) t = 0 := by
  rw [spatialPart, formPairing_sub_left, formPairing_smul_left, formPairing_self Q t]
  field_simp
  ring

omit [FiniteDimensional ℝ V] in
/-- The value of `Q` on the projection, in terms of the pairing with `t`. -/
theorem quadratic_spatialPart (Q : QuadraticForm ℝ V) {t : V} (ht : Q t ≠ 0) (x : V) :
    Q (spatialPart Q t x) = Q x - formPairing Q x t ^ 2 / Q t := by
  have h := quadratic_expand Q (1 : ℝ) (-(formPairing Q x t / Q t)) x t
  simp only [one_smul, one_pow, one_mul] at h
  rw [spatialPart, sub_eq_add_neg, ← neg_smul, h]
  field_simp
  ring

/-- **The projection has nonpositive value**: this is the key inequality, divided by `Q t`. -/
theorem quadratic_spatialPart_nonpos (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) (x : V) : Q (spatialPart Q t x) ≤ 0 := by
  have hQt : Q t ≠ 0 := ht.ne'
  rw [quadratic_spatialPart Q hQt x]
  have h := mul_self_le_formPairing_sq (Q := Q) hpos ht x
  have hdiv : Q x ≤ formPairing Q x t ^ 2 / Q t := by
    rw [le_div_iff₀ ht]
    linarith
  linarith

/-- **The reverse Cauchy–Schwarz inequality on the orthogonal complement of `t`.** The pairing of
two projections is bounded by the square root of the product of their (negated) values. -/
theorem formPairing_spatialPart_sq_le (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) (x y : V) :
    formPairing Q (spatialPart Q t x) (spatialPart Q t y) ^ 2 ≤
      (-(Q (spatialPart Q t x))) * (-(Q (spatialPart Q t y))) := by
  have hQt : Q t ≠ 0 := ht.ne'
  set u := spatialPart Q t x with hu
  set v := spatialPart Q t y with hv
  have hut : formPairing Q u t = 0 := formPairing_spatialPart_right Q hQt x
  have hvt : formPairing Q v t = 0 := formPairing_spatialPart_right Q hQt y
  have hQu : Q u ≤ 0 := quadratic_spatialPart_nonpos Q hpos ht x
  have hQv : Q v ≤ 0 := quadratic_spatialPart_nonpos Q hpos ht y
  have hexp : ∀ lam : ℝ, Q (u + lam • v) = Q u + 2 * lam * formPairing Q u v + lam ^ 2 * Q v := by
    intro lam
    rw [show u + lam • v = (1 : ℝ) • u + lam • v by simp, quadratic_expand]
    ring
  have hkey : ∀ lam : ℝ, Q (u + lam • v) ≤ 0 := by
    intro lam
    have h0 : formPairing Q (u + lam • v) t = 0 := by
      rw [formPairing_add_left, formPairing_smul_left, hut, hvt]
      ring
    by_contra hcon
    have hpos' : 0 < Q (u + lam • v) := not_le.mp hcon
    have h := mul_self_le_formPairing_sq (Q := Q) hpos ht (u + lam • v)
    rw [h0] at h
    nlinarith [h, hpos']
  rcases eq_or_ne (Q v) 0 with hv0 | hvne
  · have hB0 : formPairing Q u v = 0 := by
      by_contra hB
      have hlam := hkey ((1 - Q u) / (2 * formPairing Q u v))
      rw [hexp, hv0] at hlam
      have h2 : 2 * ((1 - Q u) / (2 * formPairing Q u v)) * formPairing Q u v = 1 - Q u := by
        field_simp
      nlinarith [hlam, h2]
    simp [hB0, hv0]
  · have hQvneg : Q v < 0 := lt_of_le_of_ne hQv hvne
    have hlam := hkey (-(formPairing Q u v) / Q v)
    rw [hexp] at hlam
    have hmul := mul_nonneg_of_nonpos_of_nonpos hlam hQvneg.le
    have hsimp : ∀ a b c : ℝ, c ≠ 0 →
        (a + 2 * (-b / c) * b + (-b / c) ^ 2 * c) * c = a * c - b ^ 2 := by
      intro a b c hc
      field_simp
      ring
    rw [hsimp (Q u) (formPairing Q u v) (Q v) hvne] at hmul
    nlinarith [hmul]

end Cone

section Sheets

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {Q : QuadraticForm ℝ V}

/-- On the cone the pairing with a positive vector never vanishes. -/
theorem formPairing_ne_zero_of_mem_positiveCone (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1)
    {t : V} (ht : 0 < Q t) {x : V} (hx : x ∈ positiveCone Q) : formPairing Q x t ≠ 0 := by
  have h := mul_self_le_formPairing_sq (Q := Q) hpos ht x
  have hpos' : 0 < Q x * Q t := mul_pos hx ht
  intro h0
  rw [h0] at h
  nlinarith [h, hpos']

/-- Every point of the cone lies on one of the two sheets cut out by a positive vector. -/
theorem mem_upper_or_mem_lower (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) {x : V} (hx : x ∈ positiveCone Q) :
    x ∈ positiveCone.upper Q t ∨ x ∈ positiveCone.lower Q t := by
  have hne := formPairing_ne_zero_of_mem_positiveCone Q hpos ht hx
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inr ⟨hx, h⟩
  · exact Or.inl ⟨hx, h⟩

/-- The cone is the union of its two sheets. -/
theorem positiveCone_eq_upper_union_lower (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1)
    {t : V} (ht : 0 < Q t) :
    positiveCone Q = positiveCone.upper Q t ∪ positiveCone.lower Q t := by
  ext x
  constructor
  · intro hx
    exact mem_upper_or_mem_lower Q hpos ht hx
  · rintro (⟨hx, -⟩ | ⟨hx, -⟩)
    · exact hx
    · exact hx

omit [FiniteDimensional ℝ V] in
/-- The two sheets are disjoint. -/
theorem upper_disjoint_lower (Q : QuadraticForm ℝ V) (t : V) :
    Disjoint (positiveCone.upper Q t) (positiveCone.lower Q t) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, hpos⟩ ⟨-, hneg⟩
  exact absurd hpos (not_lt.mpr hneg.le)

omit [FiniteDimensional ℝ V] in
/-- Negation exchanges the two sheets. -/
theorem neg_mem_upper_iff (Q : QuadraticForm ℝ V) (t x : V) :
    -x ∈ positiveCone.upper Q t ↔ x ∈ positiveCone.lower Q t := by
  have hx : Q (-x) = Q x := by
    rw [show -x = (-1 : ℝ) • x by simp, QuadraticMap.map_smul]
    simp
  have hB : formPairing Q (-x) t = -formPairing Q x t := by
    rw [show -x = (-1 : ℝ) • x by simp, formPairing_smul_left]
    ring
  rw [positiveCone.upper, positiveCone.lower]
  simp only [Set.mem_ofPred_eq]
  rw [hx, hB, neg_pos]

/-- **Two points of the same sheet pair positively.** This is the reverse Cauchy–Schwarz
inequality read through the projection off `t`. -/
theorem formPairing_pos_of_mem_upper (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) {x y : V} (hx : x ∈ positiveCone.upper Q t)
    (hy : y ∈ positiveCone.upper Q t) : 0 < formPairing Q x y := by
  obtain ⟨hQx, hBx⟩ := hx
  obtain ⟨hQy, hBy⟩ := hy
  have hQt : Q t ≠ 0 := ht.ne'
  set u := spatialPart Q t x with hu
  set v := spatialPart Q t y with hv
  set alpha : ℝ := formPairing Q x t / Q t with halpha
  set beta : ℝ := formPairing Q y t / Q t with hbeta
  have hxrep : x = alpha • t + u := by
    rw [halpha, hu, spatialPart]
    abel
  have hyrep : y = beta • t + v := by
    rw [hbeta, hv, spatialPart]
    abel
  have hut : formPairing Q u t = 0 := formPairing_spatialPart_right Q hQt x
  have hvt : formPairing Q v t = 0 := formPairing_spatialPart_right Q hQt y
  have hQu : Q u ≤ 0 := quadratic_spatialPart_nonpos Q hpos ht x
  have hQv : Q v ≤ 0 := quadratic_spatialPart_nonpos Q hpos ht y
  have hcs := formPairing_spatialPart_sq_le Q hpos ht x y
  have hQxeq : Q x = alpha ^ 2 * Q t + Q u := by
    conv_lhs => rw [hxrep, ← one_smul ℝ u]
    rw [quadratic_expand, formPairing_comm Q t u, hut]
    ring
  have hQyeq : Q y = beta ^ 2 * Q t + Q v := by
    conv_lhs => rw [hyrep, ← one_smul ℝ v]
    rw [quadratic_expand, formPairing_comm Q t v, hvt]
    ring
  have hsplit : formPairing Q x y = alpha * beta * Q t + formPairing Q u v := by
    calc formPairing Q x y = formPairing Q (alpha • t + u) (beta • t + v) := by
          rw [hxrep, hyrep]
      _ = alpha * beta * Q t + formPairing Q u v := by
          simp only [formPairing_add_left, formPairing_add_right, formPairing_smul_left,
            formPairing_smul_right, hut, formPairing_comm Q t v, hvt, formPairing_self]
          ring
  have halphaPos : 0 < alpha * Q t := by
    rw [halpha, div_mul_cancel₀ _ hQt]
    exact hBx
  have hbetaPos : 0 < beta * Q t := by
    rw [hbeta, div_mul_cancel₀ _ hQt]
    exact hBy
  have hleft : -Q u < alpha ^ 2 * Q t := by linarith
  have hright : -Q v < beta ^ 2 * Q t := by linarith
  have huNonneg : 0 ≤ -Q u := by linarith
  have hvNonneg : 0 ≤ -Q v := by linarith
  have hprod : (alpha ^ 2 * Q t) * (beta ^ 2 * Q t) = (alpha * beta * Q t) ^ 2 := by ring
  have hbetaSqPos : 0 < beta ^ 2 * Q t := by linarith
  have hbig : (-Q u) * (-Q v) < (alpha * beta * Q t) ^ 2 := by
    calc (-Q u) * (-Q v) ≤ (-Q u) * (beta ^ 2 * Q t) :=
          mul_le_mul_of_nonneg_left hright.le huNonneg
      _ < (alpha ^ 2 * Q t) * (beta ^ 2 * Q t) :=
          mul_lt_mul_of_pos_right hleft hbetaSqPos
      _ = (alpha * beta * Q t) ^ 2 := hprod
  have hAB : 0 < alpha * beta * Q t := by nlinarith [halphaPos, hbetaPos, ht]
  nlinarith [hcs, hbig, hAB, sq_abs (formPairing Q u v), hsplit]

/-- **Two points on opposite sheets pair negatively.** -/
theorem formPairing_neg_of_mem_upper_lower (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1)
    {t : V} (ht : 0 < Q t) {x y : V} (hx : x ∈ positiveCone.upper Q t)
    (hy : y ∈ positiveCone.lower Q t) : formPairing Q x y < 0 := by
  have hneg : -y ∈ positiveCone.upper Q t := (neg_mem_upper_iff Q t y).mpr hy
  have h := formPairing_pos_of_mem_upper Q hpos ht hx hneg
  rw [formPairing_neg_right] at h
  linarith

/-- **Two points of the lower sheet pair positively.** -/
theorem formPairing_pos_of_mem_lower (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) {x y : V} (hx : x ∈ positiveCone.lower Q t)
    (hy : y ∈ positiveCone.lower Q t) : 0 < formPairing Q x y := by
  rw [← neg_mem_upper_iff Q t x, ← neg_mem_upper_iff Q t y] at *
  have h := formPairing_pos_of_mem_upper Q hpos ht hx hy
  rw [formPairing_neg_left, formPairing_neg_right] at h
  simpa using h

omit [FiniteDimensional ℝ V] in
/-- A convex combination of two pairs of positive vectors with positive pairing has positive
value: the form is positive on the cone of a same-sheet pair. -/
theorem quadratic_pos_of_convexCombination (Q : QuadraticForm ℝ V) {x y : V} (hQx : 0 < Q x)
    (hQy : 0 < Q y) (hpair : 0 < formPairing Q x y) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : 0 < Q (a • x + b • y) := by
  rw [quadratic_expand]
  have hcross : 0 ≤ 2 * a * b * formPairing Q x y := by
    have hab' : 0 ≤ a * b := mul_nonneg ha hb
    nlinarith [hab', hpair]
  have hstrict : 0 < a ^ 2 * Q x + b ^ 2 * Q y := by
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1]
      simpa using hQy
    · have hterm : 0 < a ^ 2 * Q x := mul_pos (pow_pos hapos 2) hQx
      nlinarith [hterm, sq_nonneg b, hQy]
  linarith [hcross, hstrict]

/-- **Each sheet of the cone is convex.** -/
theorem convex_upper (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V} (ht : 0 < Q t) :
    Convex ℝ (positiveCone.upper Q t) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hQx, hBx⟩ := hx
  obtain ⟨hQy, hBy⟩ := hy
  have hpair : 0 < formPairing Q x y :=
    formPairing_pos_of_mem_upper Q hpos ht ⟨hQx, hBx⟩ ⟨hQy, hBy⟩
  constructor
  · exact quadratic_pos_of_convexCombination Q hQx hQy hpair ha hb hab
  · rw [formPairing_add_left, formPairing_smul_left, formPairing_smul_left]
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1]
      simpa using hBy
    · have h1 : 0 < a * formPairing Q x t := mul_pos hapos hBx
      have h2 : 0 ≤ b * formPairing Q y t := mul_nonneg hb hBy.le
      linarith

/-- **Each sheet of the cone is convex** (the lower one). -/
theorem convex_lower (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V} (ht : 0 < Q t) :
    Convex ℝ (positiveCone.lower Q t) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hQx, hBx⟩ := hx
  obtain ⟨hQy, hBy⟩ := hy
  have hpair : 0 < formPairing Q x y :=
    formPairing_pos_of_mem_lower Q hpos ht ⟨hQx, hBx⟩ ⟨hQy, hBy⟩
  constructor
  · exact quadratic_pos_of_convexCombination Q hQx hQy hpair ha hb hab
  · rw [formPairing_add_left, formPairing_smul_left, formPairing_smul_left]
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1]
      simpa using hBy
    · have h1 : a * formPairing Q x t < 0 := mul_neg_of_pos_of_neg hapos hBx
      have h2 : b * formPairing Q y t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hBy.le
      linarith

end Sheets

section Isometries

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {Q : QuadraticForm ℝ V}

/-- The orthogonal group `O(Q)` of a real quadratic form: the linear automorphisms preserving it. -/
def quadraticOrthogonalGroup (Q : QuadraticForm ℝ V) : Subgroup (V ≃ₗ[ℝ] V) where
  carrier := {f | ∀ x, Q (f x) = Q x}
  one_mem' := by
    intro x
    simp
  mul_mem' := by
    intro f g hf hg x
    rw [LinearEquiv.mul_apply, hf, hg]
  inv_mem' := by
    intro f hf x
    have h := hf (f.symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

omit [FiniteDimensional ℝ V] in
theorem mem_quadraticOrthogonalGroup_iff (Q : QuadraticForm ℝ V) (f : V ≃ₗ[ℝ] V) :
    f ∈ quadraticOrthogonalGroup Q ↔ ∀ x, Q (f x) = Q x :=
  Iff.rfl

omit [FiniteDimensional ℝ V] in
/-- An isometry preserves the pairing. -/
theorem formPairing_map (Q : QuadraticForm ℝ V) {f : V ≃ₗ[ℝ] V}
    (hf : f ∈ quadraticOrthogonalGroup Q) (x y : V) :
    formPairing Q (f x) (f y) = formPairing Q x y := by
  have h1 := quadratic_expand Q (1 : ℝ) (1 : ℝ) (f x) (f y)
  simp only [one_smul, one_pow, one_mul] at h1
  have h2 := quadratic_expand Q (1 : ℝ) (1 : ℝ) x y
  simp only [one_smul, one_pow, one_mul] at h2
  have h3 : f x + f y = f (x + y) := (map_add f x y).symm
  rw [h3, hf (x + y), hf x, hf y] at h1
  linarith [h1, h2]

end Isometries

section SheetsAction

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {Q : QuadraticForm ℝ V}

/-- Points of the cone that pair positively lie on the same sheet. -/
theorem mem_upper_iff_of_formPairing_pos (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) {u v : V} (hu : u ∈ positiveCone Q) (hv : v ∈ positiveCone Q)
    (h : 0 < formPairing Q u v) :
    (u ∈ positiveCone.upper Q t ↔ v ∈ positiveCone.upper Q t) := by
  rcases mem_upper_or_mem_lower Q hpos ht hu with h1 | h1 <;>
    rcases mem_upper_or_mem_lower Q hpos ht hv with h2 | h2
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · exact absurd h (not_lt.mpr (formPairing_neg_of_mem_upper_lower Q hpos ht h1 h2).le)
  · refine absurd h (not_lt.mpr ?_)
    rw [formPairing_comm]
    exact (formPairing_neg_of_mem_upper_lower Q hpos ht h2 h1).le
  · exact ⟨fun h3 => absurd h3.2 (not_lt.mpr h1.2.le),
      fun h3 => absurd h3.2 (not_lt.mpr h2.2.le)⟩

/-- The image of a sheet is contained in one sheet. -/
theorem image_upper_subset_sheet (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) {f : V ≃ₗ[ℝ] V} (hf : f ∈ quadraticOrthogonalGroup Q) :
    f '' positiveCone.upper Q t ⊆ positiveCone.upper Q t ∨
      f '' positiveCone.upper Q t ⊆ positiveCone.lower Q t := by
  have htUpper : t ∈ positiveCone.upper Q t := ⟨ht, by rw [formPairing_self]; exact ht⟩
  have hftCone : f t ∈ positiveCone Q := by
    change 0 < Q (f t)
    rw [hf t]
    exact ht
  have hkey : ∀ x ∈ positiveCone.upper Q t,
      (f x ∈ positiveCone.upper Q t ↔ f t ∈ positiveCone.upper Q t) := by
    intro x hx
    have hxcone : f x ∈ positiveCone Q := by
      change 0 < Q (f x)
      rw [hf x]
      exact hx.1
    refine mem_upper_iff_of_formPairing_pos Q hpos ht hxcone hftCone ?_
    rw [formPairing_map Q hf x t]
    exact hx.2
  rcases mem_upper_or_mem_lower Q hpos ht hftCone with h | h
  · left
    rintro z ⟨x, hx, rfl⟩
    exact (hkey x hx).mpr h
  · right
    rintro z ⟨x, hx, rfl⟩
    have hxcone : f x ∈ positiveCone Q := by
      change 0 < Q (f x)
      rw [hf x]
      exact hx.1
    have hnot : ¬ f x ∈ positiveCone.upper Q t :=
      fun h' => absurd ((hkey x hx).mp h').2 (not_lt.mpr h.2.le)
    rcases mem_upper_or_mem_lower Q hpos ht hxcone with h' | h'
    · exact absurd h' hnot
    · exact h'

omit [FiniteDimensional ℝ V] in
/-- The two images of the two sheets are distinct: `f` is injective and the sheets are disjoint
and nonempty. -/
theorem image_lower_ne_image_upper (Q : QuadraticForm ℝ V) {t : V} (ht : 0 < Q t)
    (f : V ≃ₗ[ℝ] V) :
    f '' positiveCone.lower Q t ≠ f '' positiveCone.upper Q t := by
  intro h
  have htUpper : t ∈ positiveCone.upper Q t := ⟨ht, by rw [formPairing_self]; exact ht⟩
  have hntLower : -t ∈ positiveCone.lower Q t := by
    rw [← neg_mem_upper_iff Q t (-t), neg_neg]
    exact htUpper
  have hmem : f (-t) ∈ f '' positiveCone.upper Q t := by
    rw [← h]
    exact ⟨-t, hntLower, rfl⟩
  obtain ⟨y, hy, hyz⟩ := hmem
  have hyy : y = -t := f.injective hyz
  rw [hyy] at hy
  exact (Set.disjoint_left.mp (upper_disjoint_lower Q t)) hy hntLower

omit [FiniteDimensional ℝ V] in
/-- The image of the lower sheet is the negation of the image of the upper one. -/
theorem image_lower_eq_neg_image_upper (Q : QuadraticForm ℝ V) {t : V} (f : V ≃ₗ[ℝ] V) :
    f '' positiveCone.lower Q t = Neg.neg '' (f '' positiveCone.upper Q t) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨f (-y), ⟨-y, (neg_mem_upper_iff Q t y).mpr hy, rfl⟩, by simp⟩
  · rintro ⟨w, ⟨v, hv, rfl⟩, hz⟩
    exact ⟨-v, (neg_mem_upper_iff Q t (-v)).mp (by simpa using hv), by
      rw [map_neg]
      exact hz⟩

omit [FiniteDimensional ℝ V] in
theorem neg_image_upper (Q : QuadraticForm ℝ V) (t : V) :
    Neg.neg '' (positiveCone.upper Q t) = positiveCone.lower Q t := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (neg_mem_upper_iff Q t (-y)).mp (by simpa using hy)
  · intro hz
    exact ⟨-z, (neg_mem_upper_iff Q t z).mpr hz, by simp⟩

omit [FiniteDimensional ℝ V] in
theorem neg_image_lower (Q : QuadraticForm ℝ V) (t : V) :
    Neg.neg '' (positiveCone.lower Q t) = positiveCone.upper Q t := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (neg_mem_upper_iff Q t y).mpr hy
  · intro hz
    exact ⟨-z, (neg_mem_upper_iff Q t (-z)).mp (by simpa using hz), by simp⟩

/-- **An isometry permutes the two sheets of the cone.** -/
theorem image_upper_eq_upper_or_lower (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) {f : V ≃ₗ[ℝ] V} (hf : f ∈ quadraticOrthogonalGroup Q) :
    f '' positiveCone.upper Q t = positiveCone.upper Q t ∨
      f '' positiveCone.upper Q t = positiveCone.lower Q t := by
  have hcone : f '' positiveCone Q = positiveCone Q := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change 0 < Q (f x)
      rw [hf x]
      exact hx
    · intro hz
      refine ⟨f.symm z, ?_, f.apply_symm_apply z⟩
      have hz' := hf (f.symm z)
      rw [f.apply_symm_apply] at hz'
      change 0 < Q (f.symm z)
      rw [← hz']
      exact hz
  rcases image_upper_subset_sheet Q hpos ht hf with hsub | hsub
  · left
    have hlower : f '' positiveCone.lower Q t ⊆ positiveCone.lower Q t := by
      rintro z ⟨x, hx, rfl⟩
      have himg : f (-x) ∈ positiveCone.upper Q t :=
        hsub ⟨-x, (neg_mem_upper_iff Q t x).mpr hx, rfl⟩
      rw [map_neg] at himg
      exact (neg_mem_upper_iff Q t (f x)).mp himg
    refine Set.eq_of_subset_of_subset hsub ?_
    intro z hz
    have hzcone : z ∈ positiveCone Q := by
      rw [positiveCone_eq_upper_union_lower Q hpos ht]
      exact Or.inl hz
    have hmem : z ∈ f '' positiveCone.upper Q t ∪ f '' positiveCone.lower Q t := by
      rw [← Set.image_union, ← positiveCone_eq_upper_union_lower Q hpos ht, hcone]
      exact hzcone
    rcases hmem with h | h
    · exact h
    · exact absurd (hlower h) (fun hmem =>
        (Set.disjoint_left.mp (upper_disjoint_lower Q t)) hz hmem)
  · right
    have hlower : f '' positiveCone.lower Q t ⊆ positiveCone.upper Q t := by
      rintro z ⟨x, hx, rfl⟩
      have himg : f (-x) ∈ positiveCone.lower Q t :=
        hsub ⟨-x, (neg_mem_upper_iff Q t x).mpr hx, rfl⟩
      rw [map_neg] at himg
      have hm := (neg_mem_upper_iff Q t (-(f x))).mpr himg
      simpa using hm
    refine Set.eq_of_subset_of_subset hsub ?_
    intro z hz
    have hzcone : z ∈ positiveCone Q := by
      rw [positiveCone_eq_upper_union_lower Q hpos ht]
      exact Or.inr hz
    have hmem : z ∈ f '' positiveCone.upper Q t ∪ f '' positiveCone.lower Q t := by
      rw [← Set.image_union, ← positiveCone_eq_upper_union_lower Q hpos ht, hcone]
      exact hzcone
    rcases hmem with h | h
    · exact h
    · exact absurd (hlower h) (fun hmem =>
        (Set.disjoint_left.mp (upper_disjoint_lower Q t)) hmem hz)

omit [FiniteDimensional ℝ V] in
/-- The two sheets are distinct, since one of them is nonempty. -/
theorem upper_ne_lower (Q : QuadraticForm ℝ V) (t : V) (ht : 0 < Q t) :
    positiveCone.upper Q t ≠ positiveCone.lower Q t := by
  intro h
  have h1 : 0 < formPairing Q t t := by rw [formPairing_self]; exact ht
  have h2 : t ∈ positiveCone.lower Q t := h ▸ (⟨ht, h1⟩ : t ∈ positiveCone.upper Q t)
  exact absurd h2.2 (not_lt.mpr h1.le)

/-- The image of the lower sheet under an isometry, in terms of the image of the upper one. -/
theorem image_lower_eq (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V} (ht : 0 < Q t)
    {f : V ≃ₗ[ℝ] V} (hf : f ∈ quadraticOrthogonalGroup Q) :
    f '' positiveCone.lower Q t =
      if f '' positiveCone.upper Q t = positiveCone.upper Q t
        then positiveCone.lower Q t else positiveCone.upper Q t := by
  by_cases h : f '' positiveCone.upper Q t = positiveCone.upper Q t
  · rw [if_pos h, image_lower_eq_neg_image_upper, h, neg_image_upper]
  · rw [if_neg h]
    have hswap : f '' positiveCone.upper Q t = positiveCone.lower Q t :=
      (image_upper_eq_upper_or_lower Q hpos ht hf).resolve_left h
    rw [image_lower_eq_neg_image_upper, hswap, neg_image_lower]

omit [FiniteDimensional ℝ V] in
/-- The image of a sheet under a product is the iterated image. -/
theorem image_upper_mul (Q : QuadraticForm ℝ V) (t : V) (f g : quadraticOrthogonalGroup Q) :
    ((f * g : quadraticOrthogonalGroup Q) : V ≃ₗ[ℝ] V) '' positiveCone.upper Q t =
      (f : V ≃ₗ[ℝ] V) '' ((g : V ≃ₗ[ℝ] V) '' positiveCone.upper Q t) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(g : V ≃ₗ[ℝ] V) y, ⟨y, hy, rfl⟩, by
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply]⟩
  · rintro ⟨w, ⟨y, hy, rfl⟩, hz⟩
    exact ⟨y, hy, by
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
      exact hz⟩

/-- The sign character of the cone: `1` on isometries preserving the sheets, `-1` on those
exchanging them. -/
noncomputable def positiveConeSign (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) (t : V)
    (ht : 0 < Q t) : quadraticOrthogonalGroup Q →* ℤˣ where
  toFun f := by
    classical
    exact if (f : V ≃ₗ[ℝ] V) '' positiveCone.upper Q t = positiveCone.upper Q t then 1 else -1
  map_one' := by
    classical
    have h : ((1 : quadraticOrthogonalGroup Q) : V ≃ₗ[ℝ] V) '' positiveCone.upper Q t =
        positiveCone.upper Q t := by
      rw [Subgroup.coe_one]
      exact Set.image_id _
    simp only [h, if_true]
  map_mul' f g := by
    classical
    have hmul := image_upper_mul Q t f g
    have hg' := image_upper_eq_upper_or_lower Q hpos ht g.2
    have hfl := image_lower_eq Q hpos ht f.2
    have hne := upper_ne_lower Q t ht
    rw [hmul]
    rcases hg' with hg' | hg'
    · rw [hg', if_pos rfl]
      by_cases hfu : (f : V ≃ₗ[ℝ] V) '' positiveCone.upper Q t = positiveCone.upper Q t <;>
        simp [hfu]
    · rw [hg', hfl]
      by_cases hfu : (f : V ≃ₗ[ℝ] V) '' positiveCone.upper Q t = positiveCone.upper Q t <;>
        simp [hfu, Ne.symm hne]

/-- **`O⁺(Q)`**: the isometries preserving each sheet of the positive cone, i.e. the stabilizer of
one sheet. -/
noncomputable def positiveConeStabilizer (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) (t : V)
    (ht : 0 < Q t) : Subgroup (quadraticOrthogonalGroup Q) :=
  MonoidHom.ker (positiveConeSign Q hpos t ht)

theorem mem_positiveConeStabilizer_iff (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) (f : quadraticOrthogonalGroup Q) :
    f ∈ positiveConeStabilizer Q hpos t ht ↔
      (f : V ≃ₗ[ℝ] V) '' positiveCone.upper Q t = positiveCone.upper Q t := by
  classical
  rw [positiveConeStabilizer, MonoidHom.mem_ker]
  constructor
  · intro h
    by_contra hcon
    rw [show positiveConeSign Q hpos t ht f
        = if (f : V ≃ₗ[ℝ] V) '' positiveCone.upper Q t = positiveCone.upper Q t then 1 else -1
        from rfl, if_neg hcon] at h
    exact absurd h (by decide : ¬ (-1 : ℤˣ) = 1)
  · intro h
    rw [show positiveConeSign Q hpos t ht f
        = if (f : V ≃ₗ[ℝ] V) '' positiveCone.upper Q t = positiveCone.upper Q t then 1 else -1
        from rfl, if_pos h]

/-- **`O⁺(Q)` has index at most two** in the orthogonal group. -/
theorem positiveConeStabilizer_index_le_two (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1)
    {t : V} (ht : 0 < Q t) : (positiveConeStabilizer Q hpos t ht).index ≤ 2 := by
  classical
  rw [positiveConeStabilizer, Subgroup.index_ker]
  calc Nat.card ↥(MonoidHom.range (positiveConeSign Q hpos t ht))
      ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- `O⁺(Q)` has finite index in `O(Q)`. -/
theorem positiveConeStabilizer_finiteIndex (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1)
    {t : V} (ht : 0 < Q t) : (positiveConeStabilizer Q hpos t ht).FiniteIndex where
  index_ne_zero := by
    classical
    rw [positiveConeStabilizer, Subgroup.index_ker]
    exact Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩

end SheetsAction

end LeanCategories.Lattices.Valued

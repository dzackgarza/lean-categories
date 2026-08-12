/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Hasse

/-!
# The norm criterion for the Hilbert symbol

Over any field of characteristic not two, the Hilbert symbol `hilbertSymbol a b` is one
exactly when `b` is a norm from `K(√a)`. The quadratic extension is not built here: the
norm condition is written elementwise as `b = x * x - a * (y * y)`.

The proof is elementary algebra plus one case split on `IsSquare a`. When `a` is a square
every element of `K` is a norm, so the criterion degenerates and the symbol is one.

The norms of a fixed `a` form a subgroup of `K`, by the Brahmagupta composition identity.
That gives multiplicativity of the symbol in the second entry whenever the first factor is
a norm. Full bilinearity is false over a general field, so it is not stated here.

Reference: Serre, *A Course in Arithmetic*, Ch. III §1.1, Proposition 1 [@Ser73, p. 20].
-/

@[expose] public section

namespace LeanCategories.Lattices.Valued

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

omit [Invertible (2 : K)] in
/-- `b` is a norm from `K(√a)`, written elementwise as `b = x * x - a * (y * y)`.

The norm form of `K(√a)` sends `x + y √a` to `x ² - a y ²`, so this says exactly that `b`
lies in the image of that form. -/
def IsNormFromSqrt (a b : K) : Prop := ∃ x y : K, b = x * x - a * (y * y)

omit [Invertible (2 : K)] in
/-- One is a norm from every quadratic extension. -/
theorem isNormFromSqrt_one (a : K) : IsNormFromSqrt a 1 := ⟨1, 0, by ring⟩

omit [Invertible (2 : K)] in
/-- Norms are closed under multiplication, by the Brahmagupta composition identity. -/
theorem IsNormFromSqrt.mul {a b c : K} (hb : IsNormFromSqrt a b) (hc : IsNormFromSqrt a c) :
    IsNormFromSqrt a (b * c) := by
  obtain ⟨x, y, rfl⟩ := hb
  obtain ⟨u, v, rfl⟩ := hc
  exact ⟨x * u + a * (y * v), x * v + y * u, by ring⟩

omit [Invertible (2 : K)] in
/-- Norms are closed under inversion: dividing a norm relation by the square of the norm
inverts it. -/
theorem IsNormFromSqrt.inv {a b : K} (hb : IsNormFromSqrt a b) : IsNormFromSqrt a b⁻¹ := by
  obtain ⟨x, y, rfl⟩ := hb
  by_cases h : x * x - a * (y * y) = 0
  · exact ⟨0, 0, by rw [h, inv_zero]; ring⟩
  · exact ⟨x / (x * x - a * (y * y)), y / (x * x - a * (y * y)), by field_simp⟩

/-- Every element is a norm from `K(√a)` when `a` is a nonzero square, since then the norm
form is `x ² - c ² y ²`, which factors and represents everything. -/
theorem isNormFromSqrt_of_isSquare {a : K} (ha : a ≠ 0) (h : IsSquare a) (b : K) :
    IsNormFromSqrt a b := by
  obtain ⟨c, rfl⟩ := h
  have hc : c ≠ 0 := by
    rintro rfl
    exact ha (mul_zero 0)
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  exact ⟨(b + 1) / 2, (b - 1) / (2 * c), by field_simp; ring⟩

omit [Invertible (2 : K)] in
/-- A norm gives a nontrivial zero of `z ² - a x ² - b y ²`, namely `(x, y, 1)`. -/
theorem hilbertSymbol_eq_one_of_isNormFromSqrt {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : IsNormFromSqrt a b) : hilbertSymbol a b = 1 := by
  classical
  obtain ⟨x, y, rfl⟩ := h
  rw [hilbertSymbol, if_neg (by simp [ha, hb]), if_pos]
  exact ⟨x, y, 1, by simp, by ring⟩

/-- **The norm criterion for the Hilbert symbol.** For nonzero `a` and `b` over a field of
characteristic not two, `hilbertSymbol a b = 1` exactly when `b` is a norm from `K(√a)`.

This is Serre, *A Course in Arithmetic*, Ch. III §1.1, Proposition 1 [@Ser73, p. 20]. -/
theorem hilbertSymbol_eq_one_iff_isNormFromSqrt {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol a b = 1 ↔ IsNormFromSqrt a b := by
  classical
  refine ⟨fun h => ?_, hilbertSymbol_eq_one_of_isNormFromSqrt ha hb⟩
  rw [hilbertSymbol, if_neg (by simp [ha, hb])] at h
  have hiso : ∃ z x y : K,
      (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 := by
    by_contra hcon
    rw [if_neg hcon] at h
    norm_num at h
  obtain ⟨z, x, y, hne, heq⟩ := hiso
  by_cases hsq : IsSquare a
  · exact isNormFromSqrt_of_isSquare ha hsq b
  · have hy : y ≠ 0 := by
      rintro rfl
      have hx : x ≠ 0 := by
        rintro rfl
        have hz : z = 0 := by
          have : z ^ 2 = 0 := by linear_combination heq
          exact pow_eq_zero_iff two_ne_zero |>.mp this
        exact hne (by simp [hz])
      exact hsq ⟨z / x, by field_simp; linear_combination -heq⟩
    exact ⟨z / y, x / y, by field_simp; linear_combination -heq⟩

omit [Invertible (2 : K)] in
/-- The Hilbert symbol of one against a nonzero element is one. -/
theorem hilbertSymbol_one_left (b : K) (hb : b ≠ 0) : hilbertSymbol 1 b = 1 := by
  rw [hilbertSymbol_comm]
  exact hilbertSymbol_one_right b hb

omit [Invertible (2 : K)] in
/-- A nonzero square has Hilbert symbol one in the first entry. -/
theorem hilbertSymbol_sq_left {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol (a * a) b = 1 := by
  have h : a * a = 1 * a ^ 2 := by ring
  rw [h, hilbertSymbol_mul_square_left 1 b ha]
  exact hilbertSymbol_one_left b hb

omit [Invertible (2 : K)] in
/-- The Hilbert symbol is multiplicative in the first entry when that entry splits off a
nonzero square. -/
theorem hilbertSymbol_mul_left_of_isSquare {a b c : K} (ha : a ≠ 0) (hc : c ≠ 0)
    (h : IsSquare a) : hilbertSymbol (a * b) c = hilbertSymbol a c * hilbertSymbol b c := by
  obtain ⟨s, rfl⟩ := h
  have hs : s ≠ 0 := by
    rintro rfl
    exact ha (mul_zero 0)
  have h1 : s * s * b = b * s ^ 2 := by ring
  rw [h1, hilbertSymbol_mul_square_left b c hs, hilbertSymbol_sq_left hs hc, one_mul]

/-- Multiplying the second entry by a norm does not change the Hilbert symbol.

The norms of `a` form a subgroup of `K`, so `b * c` is a norm exactly when `c` is. -/
theorem hilbertSymbol_mul_right_of_eq_one {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : hilbertSymbol a b = 1) : hilbertSymbol a (b * c) = hilbertSymbol a c := by
  have hnb : IsNormFromSqrt a b := (hilbertSymbol_eq_one_iff_isNormFromSqrt ha hb).mp h
  have key : hilbertSymbol a (b * c) = 1 ↔ hilbertSymbol a c = 1 := by
    rw [hilbertSymbol_eq_one_iff_isNormFromSqrt ha (mul_ne_zero hb hc),
      hilbertSymbol_eq_one_iff_isNormFromSqrt ha hc]
    refine ⟨fun h1 => ?_, fun h1 => hnb.mul h1⟩
    simpa [inv_mul_cancel_left₀ hb] using hnb.inv.mul h1
  rcases hilbertSymbol_eq_one_or_neg_one ha (mul_ne_zero hb hc) with h1 | h1 <;>
    rcases hilbertSymbol_eq_one_or_neg_one ha hc with h2 | h2 <;> simp_all

/-- Partial multiplicativity in the second entry: the symbol is multiplicative whenever the
first factor is a norm, that is, whenever it has symbol one. -/
theorem hilbertSymbol_mul_right_of_eq_one' {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : hilbertSymbol a b = 1) :
    hilbertSymbol a (b * c) = hilbertSymbol a b * hilbertSymbol a c := by
  rw [h, one_mul]
  exact hilbertSymbol_mul_right_of_eq_one ha hb hc h

/-- Partial multiplicativity in the first entry, by symmetry. -/
theorem hilbertSymbol_mul_left_of_eq_one {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : hilbertSymbol a c = 1) :
    hilbertSymbol (a * b) c = hilbertSymbol a c * hilbertSymbol b c := by
  rw [hilbertSymbol_comm (a * b), hilbertSymbol_comm a, hilbertSymbol_comm b]
  rw [hilbertSymbol_comm a] at h
  exact hilbertSymbol_mul_right_of_eq_one' hc ha hb h

end LeanCategories.Lattices.Valued

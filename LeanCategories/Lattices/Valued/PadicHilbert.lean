/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Hasse
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms

@[expose] public section

namespace LeanCategories.Lattices.Valued

universe u

variable {K : Type u} [Field K]

/-- A nonzero square has Hilbert symbol one against every nonzero element. -/
theorem hilbertSymbol_eq_one_of_isSquare_left {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : IsSquare a) : hilbertSymbol a b = 1 := by
  classical
  obtain ⟨s, rfl⟩ := h
  have hs : s ≠ 0 := by
    rintro rfl
    exact ha (mul_zero 0)
  rw [hilbertSymbol, if_neg (by simp [ha, hb]), if_pos]
  exact ⟨s, 1, 0, by simp [hs], by ring⟩

/-- A nonzero square has Hilbert symbol one in the second entry. -/
theorem hilbertSymbol_eq_one_of_isSquare_right {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : IsSquare b) : hilbertSymbol a b = 1 := by
  rw [hilbertSymbol_comm]
  exact hilbertSymbol_eq_one_of_isSquare_left hb ha h

section Padic

variable {p : ℕ} [Fact p.Prime]

open PadicInt

/-- Two is a `p`-adic unit at every odd prime. -/
theorem norm_two_padicInt (hp : p ≠ 2) : ‖(2 : ℤ_[p])‖ = 1 := by
  have h : ((2 : ℕ) : ℤ_[p]) = 2 := by norm_cast
  rw [← h, norm_natCast_eq_one_iff]
  refine (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun hdvd => ?_
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd)

/-- An approximate square root of a `p`-adic unit forces the element to be a square,
for odd `p`.

This is Hensel's lemma applied to `X ^ 2 - u`; see [@Ser73, Ch. II §3.3]. -/
theorem isSquare_of_norm_sq_sub_lt_one (hp : p ≠ 2) {u r : ℤ_[p]} (hu : ‖u‖ = 1)
    (h : ‖r ^ 2 - u‖ < 1) : IsSquare u := by
  have hr : ‖r‖ = 1 := by
    rcases eq_or_lt_of_le (norm_le_one r) with h1 | hlt
    · exact h1
    · exfalso
      have hr2 : ‖r ^ 2‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg r) hlt two_ne_zero
      have hlt1 : ‖u‖ < 1 := by
        have hsum : u = r ^ 2 + -(r ^ 2 - u) := by ring
        rw [hsum]
        exact norm_lt_one_add hr2 (by rwa [norm_neg])
      exact absurd hu (ne_of_lt hlt1)
  set F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C u with hF
  have hval : F.aeval r = r ^ 2 - u := by simp [hF]
  have hderiv : F.derivative.aeval r = 2 * r := by
    simp only [hF, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_C, sub_zero, map_mul, map_pow, Polynomial.aeval_X]
    norm_num
  have hnorm : ‖F.aeval r‖ < ‖F.derivative.aeval r‖ ^ 2 := by
    rw [hval, hderiv, norm_mul, norm_two_padicInt hp, hr]
    simpa using h
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  have hz2 : z ^ 2 - u = 0 := by simpa [hF] using hz
  exact ⟨z, by linear_combination -hz2⟩

/-- A `p`-adic unit whose residue is a square is a square, for odd `p`. -/
theorem isSquare_of_isSquare_toZMod (hp : p ≠ 2) {u : ℤ_[p]} (hu : ‖u‖ = 1)
    (h : IsSquare (toZMod u)) : IsSquare u := by
  obtain ⟨s, hs⟩ := h
  refine isSquare_of_norm_sq_sub_lt_one hp hu (r := ((s.val : ℕ) : ℤ_[p])) ?_
  have hres : toZMod (((s.val : ℕ) : ℤ_[p]) ^ 2 - u) = 0 := by
    rw [map_sub, map_pow, map_natCast, ZMod.natCast_val, ZMod.cast_id, hs]
    ring
  have hmem : ((s.val : ℕ) : ℤ_[p]) ^ 2 - u ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← maximalIdeal_eq_span_p, ← ker_toZMod]
    exact hres
  exact (norm_lt_one_iff_dvd _).mpr (Ideal.mem_span_singleton.mp hmem)

/-- The residue of a `p`-adic unit is nonzero. -/
theorem toZMod_ne_zero {u : ℤ_[p]} (hu : ‖u‖ = 1) : toZMod u ≠ 0 := by
  intro h
  have hmem : u ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← maximalIdeal_eq_span_p, ← ker_toZMod]
    exact h
  have : ‖u‖ < 1 := (norm_lt_one_iff_dvd _).mpr (Ideal.mem_span_singleton.mp hmem)
  exact absurd hu (ne_of_lt this)

/-- A `p`-adic unit is a square exactly when its residue is a square, for odd `p`. -/
theorem isSquare_iff_isSquare_toZMod (hp : p ≠ 2) {u : ℤ_[p]} (hu : ‖u‖ = 1) :
    IsSquare u ↔ IsSquare (toZMod u) :=
  ⟨fun h => h.map (toZMod : ℤ_[p] →+* ZMod p), isSquare_of_isSquare_toZMod hp hu⟩

/-- The Legendre symbol of the residue decides squareness of a `p`-adic unit, for odd `p`. -/
theorem legendreSym_residue_eq_one_iff (hp : p ≠ 2) {u : ℤ_[p]} (hu : ‖u‖ = 1) :
    legendreSym p ((toZMod u).val) = 1 ↔ IsSquare u := by
  have hcast : (((toZMod u).val : ℕ) : ZMod p) = toZMod u := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [legendreSym.eq_one_iff' (p := p) (a := (toZMod u).val)
      (by rw [hcast]; exact toZMod_ne_zero hu), hcast, isSquare_iff_isSquare_toZMod hp hu]

/-- Every nonzero `p`-adic number is a power of `p` times a `p`-adic unit. -/
theorem exists_unit_mul_p_zpow {x : ℚ_[p]} (hx : x ≠ 0) :
    ∃ u : ℤ_[p], ‖u‖ = 1 ∧ x = (p : ℚ_[p]) ^ x.valuation * (u : ℚ_[p]) := by
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hnorm : ‖x * (p : ℚ_[p]) ^ (-x.valuation)‖ = 1 := by
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_p_zpow, neg_neg]
    rw [← zpow_add₀ (ne_of_gt hp0)]
    simp
  refine ⟨⟨x * (p : ℚ_[p]) ^ (-x.valuation), le_of_eq hnorm⟩, hnorm, ?_⟩
  change x = (p : ℚ_[p]) ^ x.valuation * (x * (p : ℚ_[p]) ^ (-x.valuation))
  rw [zpow_neg]
  field_simp

/-- A `p`-adic number with even valuation and square unit part is a square. -/
theorem isSquare_of_eq_p_zpow_mul {x : ℚ_[p]} {u : ℤ_[p]} {n : ℤ}
    (hx : x = (p : ℚ_[p]) ^ (2 * n) * (u : ℚ_[p])) (h : IsSquare u) : IsSquare x := by
  obtain ⟨w, hw⟩ := h
  refine ⟨(p : ℚ_[p]) ^ n * (w : ℚ_[p]), ?_⟩
  rw [hx, hw]
  push_cast
  rw [two_mul, zpow_add₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]
  ring

/-- A `p`-adic unit that is a square in the fraction field is a square in `ℤ_[p]`. -/
theorem isSquare_padicInt_of_isSquare_coe {u : ℤ_[p]} (hu : ‖u‖ = 1)
    (h : IsSquare (u : ℚ_[p])) : IsSquare u := by
  obtain ⟨w, hw⟩ := h
  have hnorm : ‖w‖ = 1 := by
    have hmul : ‖w‖ * ‖w‖ = 1 := by
      rw [← norm_mul, ← hw, ← PadicInt.norm_def, hu]
    nlinarith [norm_nonneg w]
  refine ⟨⟨w, le_of_eq hnorm⟩, ?_⟩
  exact Subtype.ext hw

/-- For odd `p`, a `p`-adic number of even valuation is a square exactly when its unit
part is a square. -/
theorem isSquare_iff_isSquare_of_eq_p_zpow_mul {x : ℚ_[p]} {u : ℤ_[p]} {n : ℤ}
    (hu : ‖u‖ = 1) (hx : x = (p : ℚ_[p]) ^ (2 * n) * (u : ℚ_[p])) :
    IsSquare x ↔ IsSquare u := by
  refine ⟨fun h => ?_, isSquare_of_eq_p_zpow_mul hx⟩
  obtain ⟨z, hz⟩ := h
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine isSquare_padicInt_of_isSquare_coe hu ⟨z * (p : ℚ_[p]) ^ (-n), ?_⟩
  have hpow : (p : ℚ_[p]) ^ (2 * n) * ((p : ℚ_[p]) ^ (-n) * (p : ℚ_[p]) ^ (-n)) = 1 := by
    rw [← zpow_add₀ hp0, ← zpow_add₀ hp0]
    simp [two_mul]
  calc (u : ℚ_[p]) = (p : ℚ_[p]) ^ (2 * n) * (u : ℚ_[p]) *
        ((p : ℚ_[p]) ^ (-n) * (p : ℚ_[p]) ^ (-n)) := by
        rw [mul_right_comm, mul_assoc, hpow, mul_one]
    _ = z * (p : ℚ_[p]) ^ (-n) * (z * (p : ℚ_[p]) ^ (-n)) := by rw [← hx, hz]; ring

/-- The valuation of a nonzero `p`-adic square is even. -/
theorem even_valuation_of_isSquare {x : ℚ_[p]} (hx : x ≠ 0) (h : IsSquare x) :
    Even x.valuation := by
  obtain ⟨z, rfl⟩ := h
  have hz : z ≠ 0 := by
    rintro rfl
    exact hx (mul_zero 0)
  exact ⟨z.valuation, Padic.valuation_mul hz hz⟩

/-- The `p`-adic Hilbert symbol is one whenever the first entry has even valuation and
square unit part, for odd `p`. -/
theorem hilbertSymbol_padic_eq_one_of_eq_p_zpow_mul {x b : ℚ_[p]} {u : ℤ_[p]} {n : ℤ}
    (hp : p ≠ 2) (hb : b ≠ 0) (hx : x ≠ 0) (hu : ‖u‖ = 1)
    (hxu : x = (p : ℚ_[p]) ^ (2 * n) * (u : ℚ_[p]))
    (h : legendreSym p ((toZMod u).val) = 1) : hilbertSymbol x b = 1 :=
  hilbertSymbol_eq_one_of_isSquare_left hx hb
    (isSquare_of_eq_p_zpow_mul hxu ((legendreSym_residue_eq_one_iff hp hu).mp h))

end Padic

end LeanCategories.Lattices.Valued

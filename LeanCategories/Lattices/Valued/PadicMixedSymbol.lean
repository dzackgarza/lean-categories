/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.PadicUnitSymbol
public import Mathlib.Data.ZMod.IntUnitsPower

/-!
# The Hilbert symbol of a unit against the prime, at an odd prime

For an odd prime `p` the Hilbert symbol `(u, p)` of a `p`-adic unit against `p` is the
quadratic residue character of the residue of `u`. One direction is Hensel's lemma: a unit
whose residue is a residue is a square, and squares pair trivially. The other direction is
anisotropy: if `u` is not a residue then the norm form `a ² - u b ²` of the unramified
quadratic extension only takes values of even valuation, while `p` has valuation one.

Reference: Serre, *A Course in Arithmetic*, Ch. III §1.2, Theorem 1 [@Ser73, p. 20].
-/

@[expose] public section

namespace LeanCategories.Lattices.Valued

namespace Padic

open PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- The value of a `p`-adic unit in `ℚ_[p]` has norm one. -/
theorem norm_coe_eq_one {u : ℤ_[p]} (hu : ‖u‖ = 1) : ‖(u : ℚ_[p])‖ = 1 := by
  rw [← PadicInt.norm_def]; exact hu

/-- A `p`-adic unit is nonzero in `ℚ_[p]`. -/
theorem coe_ne_zero_of_norm_eq_one {u : ℤ_[p]} (hu : ‖u‖ = 1) : (u : ℚ_[p]) ≠ 0 := by
  intro h
  have hone := norm_coe_eq_one hu
  rw [h, norm_zero] at hone
  exact zero_ne_one hone

/-- For odd `p` and a non-square `p`-adic unit `u`, the element `w ² - u` is a unit: its
residue cannot vanish, since `u` is not a residue. -/
theorem norm_sq_sub_eq_one (hp : p ≠ 2) {u : ℤ_[p]} (hu : ‖u‖ = 1) (hns : ¬ IsSquare u)
    (w : ℤ_[p]) : ‖w ^ 2 - u‖ = 1 := by
  refine norm_eq_one_of_toZMod_ne_zero fun h => hns ?_
  rw [map_sub, map_pow, sub_eq_zero] at h
  exact isSquare_of_isSquare_toZMod hp hu ⟨toZMod w, by rw [← h]; ring⟩

/-- For odd `p` and a non-square `p`-adic unit `u`, the element `1 - u w ²` is a unit. -/
theorem norm_one_sub_mul_sq_eq_one (hp : p ≠ 2) {u : ℤ_[p]} (hu : ‖u‖ = 1)
    (hns : ¬ IsSquare u) (w : ℤ_[p]) : ‖1 - u * w ^ 2‖ = 1 := by
  refine norm_eq_one_of_toZMod_ne_zero fun h => hns ?_
  rw [map_sub, map_one, map_mul, map_pow, sub_eq_zero] at h
  have hw : toZMod w ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  refine isSquare_of_isSquare_toZMod hp hu ⟨(toZMod w)⁻¹, ?_⟩
  field_simp
  linear_combination -h

/-- For odd `p` and a non-square `p`-adic unit `u`, every value `a ² - u b ²` of the norm
form of `ℚ_[p](√u)`, with `a` and `b` not both zero, is a square times a unit. -/
theorem exists_sq_mul_unit_eq_normForm (hp : p ≠ 2) {u : ℤ_[p]} (hu : ‖u‖ = 1)
    (hns : ¬ IsSquare u) {a b : ℚ_[p]} (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ s m : ℚ_[p], s ≠ 0 ∧ ‖m‖ = 1 ∧ a * a - (u : ℚ_[p]) * (b * b) = s * s * m := by
  rcases le_total ‖a‖ ‖b‖ with h | h
  · have hb : b ≠ 0 := by
      rcases hab with ha | hb
      · intro hb0
        rw [hb0, norm_zero] at h
        exact ha (norm_eq_zero.mp (le_antisymm h (norm_nonneg a)))
      · exact hb
    have hbpos : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hb
    have hw : ‖a / b‖ ≤ 1 := by
      rw [norm_div]
      exact (div_le_one hbpos).mpr h
    refine ⟨b, ((⟨a / b, hw⟩ ^ 2 - u : ℤ_[p]) : ℚ_[p]), hb, ?_, ?_⟩
    · rw [← PadicInt.norm_def]
      exact norm_sq_sub_eq_one hp hu hns _
    · push_cast
      field_simp
  · have ha : a ≠ 0 := by
      rcases hab with ha | hb
      · exact ha
      · intro ha0
        rw [ha0, norm_zero] at h
        exact hb (norm_eq_zero.mp (le_antisymm h (norm_nonneg b)))
    have hapos : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
    have hw : ‖b / a‖ ≤ 1 := by
      rw [norm_div]
      exact (div_le_one hapos).mpr h
    refine ⟨a, ((1 - u * ⟨b / a, hw⟩ ^ 2 : ℤ_[p]) : ℚ_[p]), ha, ?_, ?_⟩
    · rw [← PadicInt.norm_def]
      exact norm_one_sub_mul_sq_eq_one hp hu hns _
    · push_cast
      field_simp

/-- For odd `p`, a non-square `p`-adic unit `u` does not have `p` as a norm from `√u`: the
norm form only takes values of even valuation, while `p` has valuation one. -/
theorem not_isNormFromSqrt_p (hp : p ≠ 2) {u : ℤ_[p]} (hu : ‖u‖ = 1) (hns : ¬ IsSquare u) :
    ¬ IsNormFromSqrt (u : ℚ_[p]) (p : ℚ_[p]) := by
  rintro ⟨a, b, hab⟩
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hne : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [hcon.1, hcon.2] at hab
    exact hp0 (by linear_combination hab)
  obtain ⟨s, m, hs, hm, heq⟩ := exists_sq_mul_unit_eq_normForm hp hu hns hne
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, norm_zero] at hm
    exact zero_ne_one hm
  have hval : (p : ℚ_[p]).valuation = (s * s * m).valuation := by rw [← heq, ← hab]
  rw [Padic.valuation_mul (mul_ne_zero hs hs) hm0, Padic.valuation_mul hs hs,
    valuation_eq_zero_of_norm_eq_one hm0 hm, Padic.valuation_p] at hval
  omega

/-- The Legendre symbol of the natural-number lift of a residue is the quadratic character
of that residue. -/
theorem legendreSym_val (a : ZMod p) :
    legendreSym p (a.val : ℤ) = quadraticChar (ZMod p) a := by
  rw [legendreSym]
  congr 1
  push_cast
  simp

/-- The residue character of `-1`, as a sign. It is `1` for `p ≡ 1 [MOD 4]` and `-1` for
`p ≡ 3 [MOD 4]`. -/
noncomputable def negOneChar (p : ℕ) [Fact p.Prime] : ℤˣ :=
  (quadraticChar (ZMod p)).toUnitHom (-1)

@[simp]
theorem coe_negOneChar : ((negOneChar p : ℤˣ) : ℤ) = quadraticChar (ZMod p) (-1) := by
  rw [negOneChar, MulChar.coe_toUnitHom, Units.val_neg, Units.val_one]

@[simp]
theorem coe_residueChar (x : ℚ_[p]ˣ) :
    ((residueChar x : ℤˣ) : ℤ) = quadraticChar (ZMod p) (toZMod (unitPartInt x)) := by
  rw [residueChar, MonoidHom.comp_apply, MonoidHom.comp_apply, MulChar.coe_toUnitHom,
    Units.coe_map]
  simp [unitPartHom]

/-- A nonzero `p`-adic number is its valuation power of `p` times its unit part. -/
theorem coe_eq_p_zpow_mul_unitPartInt (x : ℚ_[p]ˣ) :
    (x : ℚ_[p]) = (p : ℚ_[p]) ^ (x : ℚ_[p]).valuation * (unitPartInt x : ℚ_[p]) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpow : (p : ℚ_[p]) ^ (x : ℚ_[p]).valuation *
      (p : ℚ_[p]) ^ (-(x : ℚ_[p]).valuation) = 1 := by
    rw [← zpow_add₀ hp0]
    simp
  calc (x : ℚ_[p])
      = (x : ℚ_[p]) * ((p : ℚ_[p]) ^ (x : ℚ_[p]).valuation *
          (p : ℚ_[p]) ^ (-(x : ℚ_[p]).valuation)) := by rw [hpow, mul_one]
    _ = (p : ℚ_[p]) ^ (x : ℚ_[p]).valuation * (unitPartInt x : ℚ_[p]) := by
        rw [coe_unitPartInt]; ring

/-- The class in `ZMod 2` of an integer is the class of its remainder modulo two. -/
theorem intCast_zmod_two_eq (n : ℤ) : ((n : ZMod 2)) = ((n % 2 : ℤ) : ZMod 2) :=
  (ZMod.intCast_eq_intCast_iff _ _ _).mpr (show n % 2 = n % 2 % 2 by omega)

/-- A nonzero `p`-adic number is a representative of its square class times a square: the
representative is `p ^ (v mod 2)` times the unit part. -/
theorem coe_eq_repr_mul_sq (x : ℚ_[p]ˣ) :
    (x : ℚ_[p]) = ((p : ℚ_[p]) ^ ((x : ℚ_[p]).valuation % 2) * (unitPartInt x : ℚ_[p])) *
      ((p : ℚ_[p]) ^ ((x : ℚ_[p]).valuation / 2)) ^ 2 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hsq : ((p : ℚ_[p]) ^ ((x : ℚ_[p]).valuation / 2)) ^ 2 =
      (p : ℚ_[p]) ^ (2 * ((x : ℚ_[p]).valuation / 2)) := by
    rw [← zpow_natCast ((p : ℚ_[p]) ^ ((x : ℚ_[p]).valuation / 2)) 2, ← zpow_mul]
    norm_num [mul_comm]
  conv_lhs => rw [coe_eq_p_zpow_mul_unitPartInt x]
  rw [hsq]
  calc (p : ℚ_[p]) ^ (x : ℚ_[p]).valuation * (unitPartInt x : ℚ_[p])
      = ((p : ℚ_[p]) ^ ((x : ℚ_[p]).valuation % 2) *
          (p : ℚ_[p]) ^ (2 * ((x : ℚ_[p]).valuation / 2))) * (unitPartInt x : ℚ_[p]) := by
        rw [← zpow_add₀ hp0]
        congr 2
        omega
    _ = ((p : ℚ_[p]) ^ ((x : ℚ_[p]).valuation % 2) * (unitPartInt x : ℚ_[p])) *
          (p : ℚ_[p]) ^ (2 * ((x : ℚ_[p]).valuation / 2)) := by ring

end Padic

variable {p : ℕ} [Fact p.Prime]

open PadicInt Padic in
/-- **The mixed case of the Hilbert symbol at an odd prime.** The symbol of a `p`-adic unit
against `p` is the quadratic residue character of the residue of the unit.

A unit whose residue is a square is a square, by Hensel's lemma, and squares pair trivially.
A unit whose residue is not a square gives the unramified quadratic extension, whose norm
form only takes values of even valuation; `p` has valuation one, so it is not a norm.

This is Serre, *A Course in Arithmetic*, Ch. III §1.2, Theorem 1 [@Ser73, p. 20]. -/
theorem hilbertSymbol_unit_p (hp : p ≠ 2) {u : ℤ_[p]} (hu : ‖u‖ = 1) :
    hilbertSymbol (u : ℚ_[p]) (p : ℚ_[p]) = legendreSym p ((toZMod u).val : ℤ) := by
  have hu0 : (u : ℚ_[p]) ≠ 0 := coe_ne_zero_of_norm_eq_one hu
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  by_cases hsq : IsSquare u
  · rw [(legendreSym_residue_eq_one_iff hp hu).mpr hsq]
    exact hilbertSymbol_eq_one_of_isSquare_left hu0 hp0
      (hsq.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]))
  · have hne : hilbertSymbol (u : ℚ_[p]) (p : ℚ_[p]) ≠ 1 := fun h =>
      not_isNormFromSqrt_p hp hu hsq
        ((hilbertSymbol_eq_one_iff_isNormFromSqrt hu0 hp0).mp h)
    have hres : ((((toZMod u).val : ℤ) : ZMod p)) ≠ 0 := by
      rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
      exact toZMod_ne_zero hu
    have hleg : legendreSym p ((toZMod u).val : ℤ) ≠ 1 := fun h =>
      hsq ((legendreSym_residue_eq_one_iff hp hu).mp h)
    rcases hilbertSymbol_eq_one_or_neg_one hu0 hp0 with h | h
    · exact absurd h hne
    · rcases legendreSym.eq_one_or_neg_one p hres with h2 | h2
      · exact absurd h2 hleg
      · rw [h, h2]

/-- **The Hilbert symbol of `p` against itself, at an odd prime.** It is the quadratic
residue character of `-1`, because `(p, -p) = 1` turns the symbol `(p, p)` into `(p, -1)`. -/
theorem hilbertSymbol_p_p (hp : p ≠ 2) :
    hilbertSymbol (p : ℚ_[p]) (p : ℚ_[p]) = legendreSym p (-1) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hnorm : ‖(-1 : ℤ_[p])‖ = 1 := by simp
  have hstep : hilbertSymbol (p : ℚ_[p]) (-(p : ℚ_[p]) * (-1 : ℚ_[p])) =
      hilbertSymbol (p : ℚ_[p]) (-1 : ℚ_[p]) :=
    hilbertSymbol_mul_right_of_eq_one hp0 (neg_ne_zero.mpr hp0)
      (neg_ne_zero.mpr one_ne_zero) (hilbertSymbol_neg_self _ hp0)
  rw [show -(p : ℚ_[p]) * (-1 : ℚ_[p]) = (p : ℚ_[p]) by ring] at hstep
  have hcast : (((-1 : ℤ_[p]) : ℚ_[p])) = (-1 : ℚ_[p]) := by push_cast; ring
  have hmixed := hilbertSymbol_unit_p (u := (-1 : ℤ_[p])) hp hnorm
  rw [hcast] at hmixed
  have htz : PadicInt.toZMod (-1 : ℤ_[p]) = -1 := by simp
  rw [hstep, hilbertSymbol_comm, hmixed, htz, Padic.legendreSym_val, legendreSym]
  norm_num

open PadicInt Padic in
/-- The mixed case, written with the quadratic character of the residue field. -/
theorem hilbertSymbol_unit_p' (hp : p ≠ 2) {u : ℤ_[p]} (hu : ‖u‖ = 1) :
    hilbertSymbol (u : ℚ_[p]) (p : ℚ_[p]) = quadraticChar (ZMod p) (toZMod u) := by
  rw [hilbertSymbol_unit_p hp hu, Padic.legendreSym_val]

open PadicInt Padic in
/-- The symbol of a unit against `p` times a unit: the second unit can be absorbed, because
two units pair trivially. -/
theorem hilbertSymbol_unit_p_mul (hp : p ≠ 2) {u w : ℤ_[p]} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    hilbertSymbol (u : ℚ_[p]) ((p : ℚ_[p]) * (w : ℚ_[p])) =
      quadraticChar (ZMod p) (toZMod u) := by
  have hu0 : (u : ℚ_[p]) ≠ 0 := coe_ne_zero_of_norm_eq_one hu
  have hw0 : (w : ℚ_[p]) ≠ 0 := coe_ne_zero_of_norm_eq_one hw
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [mul_comm, hilbertSymbol_mul_right_of_eq_one hu0 hw0 hp0
    (hilbertSymbol_units_eq_one hp _ _ (norm_coe_eq_one hu) (norm_coe_eq_one hw))]
  exact hilbertSymbol_unit_p' hp hu

open PadicInt Padic in
/-- The symbol of two elements of odd valuation. The identity `(a, -a) = 1` moves the
computation to the mixed case, after a square is absorbed. -/
theorem hilbertSymbol_p_mul_p_mul (hp : p ≠ 2) {u w : ℤ_[p]} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    hilbertSymbol ((p : ℚ_[p]) * (u : ℚ_[p])) ((p : ℚ_[p]) * (w : ℚ_[p])) =
      quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) (toZMod u) *
        quadraticChar (ZMod p) (toZMod w) := by
  have hu0 : (u : ℚ_[p]) ≠ 0 := coe_ne_zero_of_norm_eq_one hu
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hA : (p : ℚ_[p]) * (u : ℚ_[p]) ≠ 0 := mul_ne_zero hp0 hu0
  have hm : ‖(-(u * w) : ℤ_[p])‖ = 1 := by
    rw [norm_neg, norm_mul, hu, hw, one_mul]
  have hm0 : ((-(u * w) : ℤ_[p]) : ℚ_[p]) ≠ 0 := coe_ne_zero_of_norm_eq_one hm
  have hsplit : (p : ℚ_[p]) * (w : ℚ_[p]) * (u : ℚ_[p]) ^ 2 =
      -((p : ℚ_[p]) * (u : ℚ_[p])) * ((-(u * w) : ℤ_[p]) : ℚ_[p]) := by
    push_cast
    ring
  have htz : toZMod (-(u * w)) = -1 * (toZMod u * toZMod w) := by
    rw [map_neg, map_mul]
    ring
  calc hilbertSymbol ((p : ℚ_[p]) * (u : ℚ_[p])) ((p : ℚ_[p]) * (w : ℚ_[p]))
      = hilbertSymbol ((p : ℚ_[p]) * (u : ℚ_[p]))
          ((p : ℚ_[p]) * (w : ℚ_[p]) * (u : ℚ_[p]) ^ 2) :=
        (hilbertSymbol_mul_square_right _ _ hu0).symm
    _ = hilbertSymbol ((p : ℚ_[p]) * (u : ℚ_[p])) (((-(u * w) : ℤ_[p]) : ℚ_[p])) := by
        rw [hsplit]
        exact hilbertSymbol_mul_right_of_eq_one hA (neg_ne_zero.mpr hA) hm0
          (hilbertSymbol_neg_self _ hA)
    _ = hilbertSymbol (((-(u * w) : ℤ_[p]) : ℚ_[p])) ((p : ℚ_[p]) * (u : ℚ_[p])) :=
        hilbertSymbol_comm _ _
    _ = quadraticChar (ZMod p) (toZMod (-(u * w))) := hilbertSymbol_unit_p_mul hp hm hu
    _ = quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) (toZMod u) *
          quadraticChar (ZMod p) (toZMod w) := by
        rw [htz, map_mul, map_mul, mul_assoc]

open PadicInt Padic in
/-- **The closed formula for the Hilbert symbol of `ℚ_[p]`, for odd `p`.**

Writing `a = p ^ α u` and `b = p ^ β v` with units `u` and `v`, the symbol is
`(-1) ^ (α β ε(p)) · (u/p) ^ β · (v/p) ^ α`, where `ε(p)` is the sign `(-1) ^ ((p-1)/2)`
recorded by `negOneChar` and `(·/p)` is the residue character. The exponents live in
`ZMod 2`, which is exactly the statement that only the parities of `α` and `β` matter.

This is Serre, *A Course in Arithmetic*, Ch. III §1.2, Theorem 1 [@Ser73, p. 20]. -/
theorem hilbertSymbol_odd_formula (hp : p ≠ 2) (x y : ℚ_[p]ˣ) :
    hilbertSymbol (x : ℚ_[p]) (y : ℚ_[p]) =
      ((negOneChar p ^ ((((x : ℚ_[p]).valuation : ZMod 2)) * (((y : ℚ_[p]).valuation : ZMod 2))) *
        residueChar x ^ (((y : ℚ_[p]).valuation : ZMod 2)) *
        residueChar y ^ (((x : ℚ_[p]).valuation : ZMod 2)) : ℤˣ) : ℤ) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hU : ‖unitPartInt x‖ = 1 := norm_unitPartInt x
  have hW : ‖unitPartInt y‖ = 1 := norm_unitPartInt y
  conv_lhs => rw [coe_eq_repr_mul_sq x, coe_eq_repr_mul_sq y]
  rw [hilbertSymbol_mul_square_left _ _ (zpow_ne_zero _ hp0),
    hilbertSymbol_mul_square_right _ _ (zpow_ne_zero _ hp0),
    intCast_zmod_two_eq (x : ℚ_[p]).valuation, intCast_zmod_two_eq (y : ℚ_[p]).valuation]
  rcases Int.emod_two_eq_zero_or_one (x : ℚ_[p]).valuation with hv2 | hv2 <;>
    rcases Int.emod_two_eq_zero_or_one (y : ℚ_[p]).valuation with hw2 | hw2 <;>
    rw [hv2, hw2]
  · simp only [Int.cast_zero, zero_mul, uzpow_zero, mul_one, one_mul, zpow_zero, Units.val_one]
    exact hilbertSymbol_units_eq_one hp _ _ (norm_coe_eq_one hU) (norm_coe_eq_one hW)
  · simp only [Int.cast_zero, Int.cast_one, uzpow_zero, uzpow_one, mul_one,
      one_mul, zpow_zero, zpow_one, coe_residueChar]
    exact hilbertSymbol_unit_p_mul hp hU hW
  · simp only [Int.cast_zero, Int.cast_one, mul_zero, uzpow_zero, uzpow_one, mul_one,
      one_mul, zpow_zero, zpow_one, coe_residueChar]
    rw [hilbertSymbol_comm]
    exact hilbertSymbol_unit_p_mul hp hW hU
  · simp only [Int.cast_one, mul_one, uzpow_one, zpow_one, Units.val_mul, coe_residueChar,
      coe_negOneChar]
    exact hilbertSymbol_p_mul_p_mul hp hU hW

open Padic in
/-- **The `p`-adic Hilbert symbol is bilinear, for odd `p`.** The closed formula makes
bilinearity exponent arithmetic: the valuation and the residue character are both
multiplicative, and the exponents add in `ZMod 2`. -/
theorem hasBilinearHilbertSymbol_of_ne_two (hp : p ≠ 2) : HasBilinearHilbertSymbol ℚ_[p] where
  map_mul_left {a b c} := by
    by_cases h0 : a = 0 ∨ b = 0 ∨ c = 0
    · rcases h0 with h0 | h0 | h0 <;> simp [hilbertSymbol, h0]
    push Not at h0
    obtain ⟨ha, hb, hc⟩ := h0
    have key : hilbertSymbol ((Units.mk0 a ha * Units.mk0 b hb : ℚ_[p]ˣ) : ℚ_[p])
          ((Units.mk0 c hc : ℚ_[p]ˣ) : ℚ_[p]) =
        hilbertSymbol ((Units.mk0 a ha : ℚ_[p]ˣ) : ℚ_[p]) ((Units.mk0 c hc : ℚ_[p]ˣ) : ℚ_[p]) *
          hilbertSymbol ((Units.mk0 b hb : ℚ_[p]ˣ) : ℚ_[p])
            ((Units.mk0 c hc : ℚ_[p]ˣ) : ℚ_[p]) := by
      have hval : ((Units.mk0 a ha * Units.mk0 b hb : ℚ_[p]ˣ) : ℚ_[p]).valuation =
          (a : ℚ_[p]).valuation + (b : ℚ_[p]).valuation := by
        rw [Units.val_mul]
        exact Padic.valuation_mul ha hb
      rw [hilbertSymbol_odd_formula hp _ _, hilbertSymbol_odd_formula hp (Units.mk0 a ha),
        hilbertSymbol_odd_formula hp (Units.mk0 b hb), ← Units.val_mul, hval, map_mul]
      congr 1
      push_cast [Units.val_mk0]
      rw [add_mul, uzpow_add, mul_uzpow, uzpow_add]
      simp only [mul_assoc, mul_left_comm]
    simpa using key

/-- For an odd prime, the `p`-adic Hilbert symbol is bilinear. -/
instance instHasBilinearHilbertSymbol {p : ℕ} [Fact p.Prime] [Fact (p ≠ 2)] :
    HasBilinearHilbertSymbol ℚ_[p] :=
  hasBilinearHilbertSymbol_of_ne_two Fact.out

end LeanCategories.Lattices.Valued

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.PadicHilbert
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The Hilbert symbol of two units at an odd prime

For an odd prime `p`, two `p`-adic units always have Hilbert symbol one. The reason is
that the form `z ² - u x ² - v y ²` is isotropic already modulo `p`: over a finite field
of odd order the value sets of `u x ²` and of `1 - v y ²` must meet, so there are residues
with `ū x̄ ² + v̄ ȳ ² = 1`. Lifting is Hensel's lemma: the value `u x ² + v y ²` of the
lifted residues is a unit congruent to one, hence a square in `ℤ_[p]`.

Reference: Serre, *A Course in Arithmetic*, Ch. III §1.2, Theorem 1 [@Ser73, p. 20].
-/

@[expose] public section

namespace LeanCategories.Lattices.Valued

namespace Padic

open PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- An odd prime has odd cardinality as the order of `ZMod p`. -/
theorem card_zmod_mod_two (hp : p ≠ 2) : Fintype.card (ZMod p) % 2 = 1 := by
  rw [ZMod.card]
  exact Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp)

/-- A nondegenerate binary form over `ZMod p` represents one, for odd `p`.

This is the isotropy of the ternary form `z ² - a x ² - b y ²` over a finite field of odd
order, in the normalised shape `z̄ = 1`. It follows from a counting argument, packaged in
Mathlib as `FiniteField.exists_root_sum_quadratic`. -/
theorem exists_sq_add_sq_eq_one (hp : p ≠ 2) {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x y : ZMod p, a * x ^ 2 + b * y ^ 2 = 1 := by
  have hf : (Polynomial.C a * Polynomial.X ^ 2).degree = 2 :=
    Polynomial.degree_C_mul_X_pow 2 ha
  have hb2 : (Polynomial.C b * Polynomial.X ^ 2).degree = 2 :=
    Polynomial.degree_C_mul_X_pow 2 hb
  have hg : (Polynomial.C b * Polynomial.X ^ 2 - Polynomial.C 1).degree = 2 := by
    rw [Polynomial.degree_sub_C (by rw [hb2]; norm_num)]
    exact hb2
  obtain ⟨x, y, h⟩ := FiniteField.exists_root_sum_quadratic hf hg (card_zmod_mod_two hp)
  refine ⟨x, y, ?_⟩
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_sub] at h
  linear_combination h

/-- A `p`-adic integer with nonzero residue is a unit. -/
theorem norm_eq_one_of_toZMod_ne_zero {w : ℤ_[p]} (h : toZMod w ≠ 0) : ‖w‖ = 1 := by
  rcases eq_or_lt_of_le (norm_le_one w) with h1 | h1
  · exact h1
  · refine absurd ?_ h
    have hmem : w ∈ Ideal.span {(p : ℤ_[p])} :=
      Ideal.mem_span_singleton.mpr ((norm_lt_one_iff_dvd w).mp h1)
    rw [← maximalIdeal_eq_span_p, ← ker_toZMod] at hmem
    exact hmem

/-- The residue of the natural-number lift of a residue is that residue. -/
theorem toZMod_natCast_val (x : ZMod p) : toZMod ((x.val : ℕ) : ℤ_[p]) = x := by
  rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]

/-- Two `p`-adic units represent one by the form `u x ² + v y ²`, for odd `p`.

The residues represent one over `ZMod p`; lifting them makes `u x ² + v y ²` a unit
congruent to one modulo `p`, hence a square in `ℤ_[p]` by Hensel's lemma. -/
theorem exists_sq_eq_add_sq (hp : p ≠ 2) {u v : ℤ_[p]} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ z x y : ℤ_[p], ‖z‖ = 1 ∧ z ^ 2 = u * x ^ 2 + v * y ^ 2 := by
  obtain ⟨x, y, hxy⟩ :=
    exists_sq_add_sq_eq_one hp (toZMod_ne_zero hu) (toZMod_ne_zero hv)
  set X : ℤ_[p] := ((x.val : ℕ) : ℤ_[p]) with hX
  set Y : ℤ_[p] := ((y.val : ℕ) : ℤ_[p]) with hY
  have hres : toZMod (u * X ^ 2 + v * Y ^ 2) = 1 := by
    rw [map_add, map_mul, map_mul, map_pow, map_pow, hX, hY, toZMod_natCast_val,
      toZMod_natCast_val]
    exact hxy
  have hnorm : ‖u * X ^ 2 + v * Y ^ 2‖ = 1 :=
    norm_eq_one_of_toZMod_ne_zero (by rw [hres]; exact one_ne_zero)
  obtain ⟨z, hz⟩ := isSquare_of_isSquare_toZMod hp hnorm (by rw [hres]; exact ⟨1, (one_mul 1).symm⟩)
  refine ⟨z, X, Y, ?_, by rw [sq]; exact hz.symm⟩
  have : ‖z‖ * ‖z‖ = 1 := by rw [← norm_mul, ← hz, hnorm]
  nlinarith [norm_nonneg z]

end Padic

open PadicInt in
/-- **Two `p`-adic units have Hilbert symbol one, for odd `p`.**

The unit case of the local Hilbert symbol computation: at an odd prime the form
`z ² - u x ² - v y ²` with unit coefficients is isotropic, since it is already isotropic
modulo `p` and the solution lifts by Hensel's lemma.

This is Serre, *A Course in Arithmetic*, Ch. III §1.2, Theorem 1 [@Ser73, p. 20]. -/
theorem hilbertSymbol_units_eq_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (u v : ℚ_[p])
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : hilbertSymbol u v = 1 := by
  classical
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv
  obtain ⟨z, x, y, hz, hsq⟩ :=
    Padic.exists_sq_eq_add_sq (u := ⟨u, le_of_eq hu⟩) (v := ⟨v, le_of_eq hv⟩) hp hu hv
  have hz0 : (z : ℚ_[p]) ≠ 0 := by
    intro h
    rw [PadicInt.norm_def, h, norm_zero] at hz
    exact zero_ne_one hz
  rw [hilbertSymbol, if_neg (by simp [hu0, hv0]), if_pos]
  refine ⟨(z : ℚ_[p]), (x : ℚ_[p]), (y : ℚ_[p]), by simp [hz0], ?_⟩
  have hcast : ((z ^ 2 : ℤ_[p]) : ℚ_[p]) =
      ((⟨u, le_of_eq hu⟩ * x ^ 2 + ⟨v, le_of_eq hv⟩ * y ^ 2 : ℤ_[p]) : ℚ_[p]) := by
    rw [hsq]
  push_cast at hcast
  linear_combination hcast

namespace Padic

variable {p : ℕ} [Fact p.Prime]

/-- The unit part `x * p ^ (-v x)` of a nonzero `p`-adic number has norm one. -/
theorem norm_mul_p_zpow_neg_valuation (x : ℚ_[p]ˣ) :
    ‖(x : ℚ_[p]) * (p : ℚ_[p]) ^ (-(x : ℚ_[p]).valuation)‖ = 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [norm_mul, Padic.norm_eq_zpow_neg_valuation (Units.ne_zero x), Padic.norm_p_zpow,
    neg_neg, ← zpow_add₀ (ne_of_gt hp0)]
  simp

/-- The unit part of a nonzero `p`-adic number, as a `p`-adic integer. -/
noncomputable def unitPartInt (x : ℚ_[p]ˣ) : ℤ_[p] :=
  ⟨(x : ℚ_[p]) * (p : ℚ_[p]) ^ (-(x : ℚ_[p]).valuation),
    le_of_eq (norm_mul_p_zpow_neg_valuation x)⟩

@[simp]
theorem coe_unitPartInt (x : ℚ_[p]ˣ) :
    ((unitPartInt x : ℤ_[p]) : ℚ_[p]) = (x : ℚ_[p]) * (p : ℚ_[p]) ^ (-(x : ℚ_[p]).valuation) :=
  rfl

/-- The unit part of a nonzero `p`-adic number has norm one. -/
theorem norm_unitPartInt (x : ℚ_[p]ˣ) : ‖unitPartInt x‖ = 1 := by
  rw [PadicInt.norm_def, coe_unitPartInt]
  exact norm_mul_p_zpow_neg_valuation x

/-- The unit part of a nonzero `p`-adic number, as a unit of `ℤ_[p]`. -/
noncomputable def unitPart (x : ℚ_[p]ˣ) : ℤ_[p]ˣ :=
  (PadicInt.isUnit_iff.mpr (norm_unitPartInt x)).unit

@[simp]
theorem coe_unitPart (x : ℚ_[p]ˣ) : ((unitPart x : ℤ_[p]ˣ) : ℤ_[p]) = unitPartInt x :=
  IsUnit.unit_spec _

/-- The unit part is multiplicative, because the valuation is additive. -/
theorem unitPart_mul (x y : ℚ_[p]ˣ) : unitPart (x * y) = unitPart x * unitPart y := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine Units.ext (Subtype.ext ?_)
  rw [Units.val_mul, PadicInt.coe_mul, coe_unitPart, coe_unitPart, coe_unitPart,
    coe_unitPartInt, coe_unitPartInt, coe_unitPartInt]
  rw [Units.val_mul, Padic.valuation_mul (Units.ne_zero x) (Units.ne_zero y), neg_add,
    zpow_add₀ hp0]
  ring

/-- The unit part as a group homomorphism from the nonzero `p`-adic numbers. -/
noncomputable def unitPartHom : ℚ_[p]ˣ →* ℤ_[p]ˣ :=
  MonoidHom.mk' unitPart unitPart_mul

/-- A nonzero `p`-adic number of even valuation is that power of `p` times its unit part. -/
theorem eq_p_zpow_mul_unitPartInt {x : ℚ_[p]ˣ} {n : ℤ} (hn : (x : ℚ_[p]).valuation = n + n) :
    (x : ℚ_[p]) = (p : ℚ_[p]) ^ (2 * n) * (unitPartInt x : ℚ_[p]) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpow : (p : ℚ_[p]) ^ (2 * n) * (p : ℚ_[p]) ^ (-(n + n)) = 1 := by
    rw [← zpow_add₀ hp0]
    norm_num [two_mul]
  calc (x : ℚ_[p])
      = (x : ℚ_[p]) * ((p : ℚ_[p]) ^ (2 * n) * (p : ℚ_[p]) ^ (-(n + n))) := by
        rw [hpow, mul_one]
    _ = (p : ℚ_[p]) ^ (2 * n) * (unitPartInt x : ℚ_[p]) := by
        rw [coe_unitPartInt, hn]
        ring

/-- Squares of units of `ℚ_[p]` are exactly the units whose value is a square. -/
theorem isSquare_iff_isSquare_coe (x : ℚ_[p]ˣ) : IsSquare x ↔ IsSquare (x : ℚ_[p]) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(y : ℚ_[p]), by push_cast; ring⟩
  · rintro ⟨z, hz⟩
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hz
      exact Units.ne_zero x hz
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩

/-- A nonzero `p`-adic number is a square exactly when its valuation is even and its unit
part is a square. -/
theorem isSquare_iff_even_valuation_and (x : ℚ_[p]ˣ) :
    IsSquare x ↔ Even (x : ℚ_[p]).valuation ∧ IsSquare (unitPartInt x) := by
  rw [isSquare_iff_isSquare_coe]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := even_valuation_of_isSquare (Units.ne_zero x) h
    exact ⟨⟨n, hn⟩, (isSquare_iff_isSquare_of_eq_p_zpow_mul (norm_unitPartInt x)
      (eq_p_zpow_mul_unitPartInt hn)).mp h⟩
  · rintro ⟨⟨n, hn⟩, h2⟩
    exact isSquare_of_eq_p_zpow_mul (eq_p_zpow_mul_unitPartInt hn) h2

/-- The valuation modulo two, as a homomorphism to `Multiplicative (ZMod 2)`. -/
noncomputable def valuationModTwo : ℚ_[p]ˣ →* Multiplicative (ZMod 2) :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (((x : ℚ_[p]).valuation : ZMod 2)))
    fun x y => by
      simp only [Units.val_mul, Padic.valuation_mul (Units.ne_zero x) (Units.ne_zero y)]
      rw [Int.cast_add, ofAdd_add]

@[simp]
theorem valuationModTwo_apply (x : ℚ_[p]ˣ) :
    valuationModTwo x = Multiplicative.ofAdd (((x : ℚ_[p]).valuation : ZMod 2)) := rfl

/-- The valuation is even exactly when its class modulo two is trivial. -/
theorem valuationModTwo_eq_one_iff (x : ℚ_[p]ˣ) :
    valuationModTwo x = 1 ↔ Even (x : ℚ_[p]).valuation := by
  simp [ZMod.intCast_zmod_eq_zero_iff_dvd, even_iff_two_dvd]

/-- The quadratic residue character of the unit part of a nonzero `p`-adic number. -/
noncomputable def residueChar : ℚ_[p]ˣ →* ℤˣ :=
  (quadraticChar (ZMod p)).toUnitHom.comp
    ((Units.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p).toMonoidHom).comp unitPartHom)

/-- For odd `p`, the residue character of a nonzero `p`-adic number is trivial exactly when
its unit part is a square. -/
theorem residueChar_eq_one_iff (hp : p ≠ 2) (x : ℚ_[p]ˣ) :
    residueChar x = 1 ↔ IsSquare (unitPartInt x) := by
  rw [← Units.val_eq_one, residueChar, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulChar.coe_toUnitHom]
  have hcoe : ((Units.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p).toMonoidHom)
      (unitPartHom x) : ZMod p) = PadicInt.toZMod (unitPartInt x) := by
    rw [Units.coe_map]
    simp [unitPartHom]
  rw [hcoe, quadraticChar_one_iff_isSquare (toZMod_ne_zero (norm_unitPartInt x)),
    ← isSquare_iff_isSquare_toZMod hp (norm_unitPartInt x)]

/-- The square-class invariants of a nonzero `p`-adic number: the parity of its valuation
together with the quadratic residue character of its unit part. -/
noncomputable def squareClassHom : ℚ_[p]ˣ →* Multiplicative (ZMod 2) × ℤˣ :=
  valuationModTwo.prod residueChar

/-- For odd `p`, the square-class invariants are trivial exactly on squares. -/
theorem squareClassHom_eq_one_iff (hp : p ≠ 2) (x : ℚ_[p]ˣ) :
    squareClassHom x = 1 ↔ IsSquare x := by
  rw [squareClassHom, MonoidHom.prod_apply, Prod.mk_eq_one, valuationModTwo_eq_one_iff,
    residueChar_eq_one_iff hp, isSquare_iff_even_valuation_and]

/-- For odd `p`, the kernel of the square-class invariants is the subgroup of squares. -/
theorem ker_squareClassHom (hp : p ≠ 2) :
    (squareClassHom (p := p)).ker = Subgroup.square ℚ_[p]ˣ := by
  ext x
  rw [MonoidHom.mem_ker, squareClassHom_eq_one_iff hp, Subgroup.mem_square]

/-- A `p`-adic number of norm one has valuation zero. -/
theorem valuation_eq_zero_of_norm_eq_one {y : ℚ_[p]} (hy0 : y ≠ 0) (hy : ‖y‖ = 1) :
    y.valuation = 0 := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hval : ((p : ℝ) ^ (-y.valuation)) = (p : ℝ) ^ (0 : ℤ) := by
    rw [← Padic.norm_eq_zpow_neg_valuation hy0, hy, zpow_zero]
  have := (zpow_right_strictMono₀ h1).injective hval
  omega

/-- The prime `p` as a nonzero `p`-adic number. -/
noncomputable def pUnit (p : ℕ) [Fact p.Prime] : ℚ_[p]ˣ :=
  Units.mk0 (p : ℚ_[p]) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

@[simp]
theorem coe_pUnit : ((pUnit p : ℚ_[p]ˣ) : ℚ_[p]) = (p : ℚ_[p]) := rfl

/-- The unit part of `p` is one. -/
theorem unitPart_pUnit : unitPart (pUnit p) = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine Units.ext (Subtype.ext ?_)
  rw [coe_unitPart, coe_unitPartInt, coe_pUnit, Padic.valuation_p, zpow_neg, zpow_one]
  field_simp
  simp

/-- The square-class invariants of `p`: odd valuation and trivial residue character. -/
theorem squareClassHom_pUnit : squareClassHom (pUnit p) = (Multiplicative.ofAdd 1, 1) := by
  rw [squareClassHom, MonoidHom.prod_apply, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [valuationModTwo_apply, coe_pUnit, Padic.valuation_p]
    norm_num
  · rw [residueChar, MonoidHom.comp_apply, MonoidHom.comp_apply,
      show unitPartHom (pUnit p) = 1 from unitPart_pUnit, map_one, map_one]

/-- For odd `p`, some `p`-adic unit is not a square: a non-residue modulo `p` lifts. -/
theorem exists_nonresidue (hp : p ≠ 2) :
    ∃ x : ℚ_[p]ˣ, squareClassHom x = (1, -1) := by
  obtain ⟨a, ha⟩ : ∃ a : ZMod p, ¬IsSquare a := by
    refine FiniteField.exists_nonsquare ?_
    rw [ZMod.ringChar_zmod_n]
    exact hp
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha ⟨0, (mul_zero 0).symm⟩
  have hres : PadicInt.toZMod ((a.val : ℕ) : ℤ_[p]) = a := toZMod_natCast_val a
  have hnorm : ‖((a.val : ℕ) : ℤ_[p])‖ = 1 :=
    norm_eq_one_of_toZMod_ne_zero (by rw [hres]; exact ha0)
  have hqnorm : ‖((((a.val : ℕ) : ℤ_[p]) : ℚ_[p]))‖ = 1 := by
    rw [← PadicInt.norm_def]; exact hnorm
  have hq0 : ((((a.val : ℕ) : ℤ_[p]) : ℚ_[p])) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hqnorm
    exact zero_ne_one hqnorm
  obtain ⟨x, hx⟩ : ∃ x : ℚ_[p]ˣ, (x : ℚ_[p]) = ((((a.val : ℕ) : ℤ_[p]) : ℚ_[p])) :=
    ⟨Units.mk0 _ hq0, rfl⟩
  refine ⟨x, ?_⟩
  have hval : (x : ℚ_[p]).valuation = 0 := by
    rw [hx]
    exact valuation_eq_zero_of_norm_eq_one hq0 hqnorm
  have hunit : unitPartInt x = ((a.val : ℕ) : ℤ_[p]) := by
    refine Subtype.ext ?_
    rw [coe_unitPartInt, hval, hx]
    simp
  rw [squareClassHom, MonoidHom.prod_apply, Prod.mk.injEq]
  refine ⟨by rw [valuationModTwo_apply, hval]; norm_num, ?_⟩
  have hne : residueChar x ≠ 1 := by
    intro hone
    rw [residueChar_eq_one_iff hp, hunit] at hone
    exact ha (hres ▸ hone.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p))
  rcases Int.units_eq_one_or (residueChar x) with h | h
  · exact absurd h hne
  · exact h

/-- For odd `p`, every value pair of the square-class invariants is already attained inside
the subgroup generated by `p` and a unit non-residue. -/
theorem exists_mem_closure_squareClassHom_eq (p : ℕ) [Fact p.Prime] {n : ℚ_[p]ˣ}
    (hn : squareClassHom n = (1, -1)) (c : Multiplicative (ZMod 2) × ℤˣ) :
    ∃ y ∈ Subgroup.closure ({pUnit p, n} : Set ℚ_[p]ˣ), squareClassHom y = c := by
  have hpmem : pUnit p ∈ Subgroup.closure ({pUnit p, n} : Set ℚ_[p]ˣ) :=
    Subgroup.subset_closure (by simp)
  have hnmem : n ∈ Subgroup.closure ({pUnit p, n} : Set ℚ_[p]ˣ) :=
    Subgroup.subset_closure (by simp)
  obtain ⟨c, d⟩ := c
  have hc : c = 1 ∨ c = Multiplicative.ofAdd 1 := by
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (Multiplicative.toAdd c) with h | h
    · exact Or.inl (Multiplicative.toAdd.injective (by rw [h]; rfl))
    · exact Or.inr (Multiplicative.toAdd.injective (by rw [h]; rfl))
  rcases hc with rfl | rfl <;> rcases Int.units_eq_one_or d with rfl | rfl
  · exact ⟨1, one_mem _, map_one _⟩
  · exact ⟨n, hnmem, hn⟩
  · exact ⟨pUnit p, hpmem, squareClassHom_pUnit⟩
  · exact ⟨pUnit p * n, mul_mem hpmem hnmem,
      by rw [map_mul, squareClassHom_pUnit, hn]; simp⟩

/-- For odd `p`, the square-class invariants are surjective: `p` and a unit non-residue
realise all four value pairs. -/
theorem squareClassHom_surjective (hp : p ≠ 2) :
    Function.Surjective (squareClassHom (p := p)) := by
  obtain ⟨n, hn⟩ := exists_nonresidue hp
  intro c
  obtain ⟨y, -, hy⟩ := exists_mem_closure_squareClassHom_eq p hn c
  exact ⟨y, hy⟩

/-- **The square classes of `ℚ_[p]` for odd `p`.** The square-class group is the Klein
four-group: the parity of the valuation and the residue character of the unit part are
independent invariants, realised by `p` and by a unit non-residue.

This is Serre, *A Course in Arithmetic*, Ch. II §3.3, Theorem 3 [@Ser73, p. 17]. -/
noncomputable def squareClassEquiv (hp : p ≠ 2) :
    PadicSquareClass p ≃* Multiplicative (ZMod 2) × ℤˣ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_squareClassHom hp).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (squareClassHom_surjective hp))

/-- For odd `p`, the square-class group of `ℚ_[p]` has order four. -/
theorem card_squareClass (hp : p ≠ 2) : Nat.card (PadicSquareClass p) = 4 := by
  rw [Nat.card_congr (squareClassEquiv hp).toEquiv, Nat.card_prod,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2), Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- For odd `p`, the square-class group of `ℚ_[p]` is generated by the class of `p` and the
class of a unit non-residue. -/
theorem closure_squareClass_eq_top (hp : p ≠ 2) :
    ∃ n : ℚ_[p]ˣ, Subgroup.closure
      ({fieldSquareClass (pUnit p), fieldSquareClass n} : Set (PadicSquareClass p)) = ⊤ := by
  obtain ⟨n, hn⟩ := exists_nonresidue hp
  refine ⟨n, eq_top_iff.mpr fun q _ => ?_⟩
  refine Quotient.inductionOn' q fun x => ?_
  change fieldSquareClass x ∈ _
  obtain ⟨y, hymem, hy⟩ := exists_mem_closure_squareClassHom_eq p hn (squareClassHom x)
  have hker : x⁻¹ * y ∈ Subgroup.square ℚ_[p]ˣ := by
    rw [← ker_squareClassHom hp, MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
  have heq : fieldSquareClass x = fieldSquareClass y :=
    QuotientGroup.eq.mpr hker
  have himg : fieldSquareClass y ∈ Subgroup.closure
      ({fieldSquareClass (pUnit p), fieldSquareClass n} : Set (PadicSquareClass p)) := by
    have := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.square ℚ_[p]ˣ)) hymem
    rwa [MonoidHom.map_closure, Set.image_pair] at this
  exact heq ▸ himg

end Padic

end LeanCategories.Lattices.Valued

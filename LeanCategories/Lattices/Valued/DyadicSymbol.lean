/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DyadicSquares
public import LeanCategories.Lattices.Valued.PadicMixedSymbol

/-!
# The square classes of the dyadic field

At the prime two a dyadic unit is a square exactly when it is congruent to one modulo
eight. The residue modulo eight is therefore a complete invariant of the square class of a
unit, and together with the parity of the valuation it is a complete invariant of the
square class of a nonzero dyadic number. There are eight square classes, represented by
`±1`, `±5`, `±2`, `±10`.

Reference: Serre, *A Course in Arithmetic*, Ch. II §3.3, Theorem 4 [@Ser73, p. 17].
-/

@[expose] public section

namespace LeanCategories.Lattices.Valued

namespace Padic

open PadicInt

/-! ## The residue of a dyadic unit modulo eight -/

/-- The residue modulo eight of a dyadic unit, as a multiplicative invariant. -/
noncomputable def dyadicUnitClass : ℤ_[2]ˣ →* (ZMod 8)ˣ :=
  Units.map (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)).toMonoidHom

@[simp]
theorem coe_dyadicUnitClass (u : ℤ_[2]ˣ) :
    ((dyadicUnitClass u : (ZMod 8)ˣ) : ZMod 8) = toZModPow 3 (u : ℤ_[2]) := by
  rw [dyadicUnitClass, Units.coe_map]
  rfl

/-- **The residue modulo eight detects squares of dyadic units.** A dyadic unit is a square
exactly when its residue modulo eight is trivial. -/
theorem dyadicUnitClass_eq_one_iff (u : ℤ_[2]ˣ) :
    dyadicUnitClass u = 1 ↔ IsSquare (u : ℤ_[2]) := by
  rw [← Units.val_eq_one, coe_dyadicUnitClass,
    ← isSquare_iff_toZModPow_three_eq_one (PadicInt.isUnit_iff.mp u.isUnit)]

/-! ## The square-class invariants of a nonzero dyadic number -/

/-- The residue modulo eight of the unit part of a nonzero dyadic number. -/
noncomputable def dyadicResidue : ℚ_[2]ˣ →* (ZMod 8)ˣ := dyadicUnitClass.comp unitPartHom

@[simp]
theorem coe_dyadicResidue (x : ℚ_[2]ˣ) :
    ((dyadicResidue x : (ZMod 8)ˣ) : ZMod 8) = toZModPow 3 (unitPartInt x) := by
  rw [dyadicResidue, MonoidHom.comp_apply, coe_dyadicUnitClass]
  congr 1

/-- The residue modulo eight of the unit part detects square unit parts. -/
theorem dyadicResidue_eq_one_iff (x : ℚ_[2]ˣ) :
    dyadicResidue x = 1 ↔ IsSquare (unitPartInt x) := by
  rw [← Units.val_eq_one, coe_dyadicResidue,
    ← isSquare_iff_toZModPow_three_eq_one (norm_unitPartInt x)]

/-- The square-class invariants of a nonzero dyadic number: the parity of the valuation
together with the residue modulo eight of the unit part. -/
noncomputable def dyadicSquareClassHom : ℚ_[2]ˣ →* Multiplicative (ZMod 2) × (ZMod 8)ˣ :=
  valuationModTwo.prod dyadicResidue

@[simp]
theorem dyadicSquareClassHom_apply (x : ℚ_[2]ˣ) :
    dyadicSquareClassHom x = (valuationModTwo x, dyadicResidue x) := rfl

/-- **The dyadic square-class invariants are trivial exactly on squares.** -/
theorem dyadicSquareClassHom_eq_one_iff (x : ℚ_[2]ˣ) :
    dyadicSquareClassHom x = 1 ↔ IsSquare x := by
  rw [dyadicSquareClassHom_apply, Prod.mk_eq_one, valuationModTwo_eq_one_iff,
    dyadicResidue_eq_one_iff, isSquare_iff_even_valuation_and]

/-- The kernel of the dyadic square-class invariants is the subgroup of squares. -/
theorem ker_dyadicSquareClassHom :
    (dyadicSquareClassHom).ker = Subgroup.square ℚ_[2]ˣ := by
  ext x
  rw [MonoidHom.mem_ker, dyadicSquareClassHom_eq_one_iff, Subgroup.mem_square]

/-- Two nonzero dyadic numbers with the same square-class invariants differ by a square. -/
theorem exists_sq_of_dyadicSquareClassHom_eq {x y : ℚ_[2]ˣ}
    (h : dyadicSquareClassHom x = dyadicSquareClassHom y) : ∃ s : ℚ_[2]ˣ, x = y * s ^ 2 := by
  have hone : dyadicSquareClassHom (y⁻¹ * x) = 1 := by
    rw [map_mul, h, ← map_mul, inv_mul_cancel, map_one]
  obtain ⟨s, hs⟩ := (dyadicSquareClassHom_eq_one_iff _).mp hone
  rw [← sq] at hs
  exact ⟨s, by rw [← hs, mul_inv_cancel_left]⟩

/-! ## Representatives of the eight square classes -/

/-- A dyadic unit, viewed as a nonzero dyadic number. -/
noncomputable def unitsCoeHom : ℤ_[2]ˣ →* ℚ_[2]ˣ :=
  Units.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]).toMonoidHom

@[simp]
theorem coe_unitsCoeHom (u : ℤ_[2]ˣ) : ((unitsCoeHom u : ℚ_[2]ˣ) : ℚ_[2]) = (u : ℤ_[2]) := by
  rw [unitsCoeHom, Units.coe_map]
  rfl

/-- A dyadic unit has valuation zero. -/
theorem valuation_unitsCoeHom (u : ℤ_[2]ˣ) :
    ((unitsCoeHom u : ℚ_[2]ˣ) : ℚ_[2]).valuation = 0 := by
  refine valuation_eq_zero_of_norm_eq_one (Units.ne_zero _) ?_
  rw [coe_unitsCoeHom, ← PadicInt.norm_def]
  exact PadicInt.isUnit_iff.mp u.isUnit

/-- A dyadic unit is its own unit part. -/
theorem unitPartInt_unitsCoeHom (u : ℤ_[2]ˣ) : unitPartInt (unitsCoeHom u) = (u : ℤ_[2]) := by
  refine Subtype.ext ?_
  rw [coe_unitPartInt, valuation_unitsCoeHom, coe_unitsCoeHom]
  simp


theorem dyadicSquareClassHom_unitsCoeHom (u : ℤ_[2]ˣ) :
    dyadicSquareClassHom (unitsCoeHom u) = (1, dyadicUnitClass u) := by
  rw [dyadicSquareClassHom_apply]
  refine Prod.ext ?_ ?_
  · rw [valuationModTwo_apply, valuation_unitsCoeHom]
    rfl
  · refine Units.ext ?_
    rw [coe_dyadicResidue, unitPartInt_unitsCoeHom, coe_dyadicUnitClass]

/-- The square-class invariants of two: odd valuation and trivial residue. -/
theorem dyadicSquareClassHom_pUnit :
    dyadicSquareClassHom (pUnit 2) = (Multiplicative.ofAdd 1, 1) := by
  rw [dyadicSquareClassHom_apply]
  refine Prod.ext ?_ ?_
  · rw [valuationModTwo_apply, coe_pUnit, Padic.valuation_p]
    norm_num
  · rw [dyadicResidue, MonoidHom.comp_apply,
      show unitPartHom (pUnit 2) = 1 from unitPart_pUnit, map_one]

/-- Five is a dyadic unit. -/
theorem norm_five_padicIntTwo : ‖(5 : ℤ_[2])‖ = 1 := by
  have h : ((5 : ℕ) : ℤ_[2]) = 5 := by norm_cast
  rw [← h, PadicInt.norm_natCast_eq_one_iff]
  decide

/-- Five as a dyadic unit. -/
noncomputable def fiveUnit : ℤ_[2]ˣ := (PadicInt.isUnit_iff.mpr norm_five_padicIntTwo).unit

@[simp]
theorem coe_fiveUnit : (fiveUnit : ℤ_[2]) = 5 := IsUnit.unit_spec _


theorem coe_dyadicUnitClass_neg (u : ℤ_[2]ˣ) :
    ((dyadicUnitClass (-u) : (ZMod 8)ˣ) : ZMod 8) =
      -((dyadicUnitClass u : (ZMod 8)ˣ) : ZMod 8) := by
  rw [coe_dyadicUnitClass, coe_dyadicUnitClass, Units.val_neg, map_neg]


theorem coe_dyadicUnitClass_one : ((dyadicUnitClass 1 : (ZMod 8)ˣ) : ZMod 8) = 1 := by
  rw [map_one, Units.val_one]

/-- The residue of five modulo eight. -/
theorem toZModPow_three_five : toZModPow 3 (5 : ℤ_[2]) = 5 := by
  have h : ((5 : ℕ) : ℤ_[2]) = 5 := by norm_cast
  rw [← h, map_natCast]
  decide


theorem coe_dyadicUnitClass_fiveUnit :
    ((dyadicUnitClass fiveUnit : (ZMod 8)ˣ) : ZMod 8) = 5 := by
  rw [coe_dyadicUnitClass, coe_fiveUnit, toZModPow_three_five]

/-- Every residue modulo eight of a unit is realised by a dyadic unit: the four residues
are those of `1`, `-1`, `5` and `-5`. -/
theorem exists_dyadicUnitClass_eq (n : (ZMod 8)ˣ) : ∃ u : ℤ_[2]ˣ, dyadicUnitClass u = n := by
  obtain ⟨m, hm⟩ := isUnit_iff_exists_inv.mp n.isUnit
  have hcases : ∀ b : ZMod 8, (∃ c, b * c = 1) → b = 1 ∨ b = -1 ∨ b = 5 ∨ b = -5 := by decide
  rcases hcases (n : ZMod 8) ⟨m, hm⟩ with h | h | h | h
  · exact ⟨1, Units.ext (by rw [coe_dyadicUnitClass_one, h])⟩
  · exact ⟨-1, Units.ext (by rw [coe_dyadicUnitClass_neg, coe_dyadicUnitClass_one, h])⟩
  · exact ⟨fiveUnit, Units.ext (by rw [coe_dyadicUnitClass_fiveUnit, h])⟩
  · exact ⟨-fiveUnit, Units.ext (by rw [coe_dyadicUnitClass_neg, coe_dyadicUnitClass_fiveUnit, h])⟩

/-- **The square-class invariants of the dyadic field are surjective.** Both the parity of
the valuation and the residue of the unit part are realised, independently. -/
theorem dyadicSquareClassHom_surjective : Function.Surjective dyadicSquareClassHom := by
  rintro ⟨a, n⟩
  obtain ⟨u, hu⟩ := exists_dyadicUnitClass_eq n
  have ha : a = 1 ∨ a = Multiplicative.ofAdd 1 := by
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (Multiplicative.toAdd a) with h | h
    · exact Or.inl (Multiplicative.toAdd.injective (by rw [h]; rfl))
    · exact Or.inr (Multiplicative.toAdd.injective (by rw [h]; rfl))
  rcases ha with rfl | rfl
  · exact ⟨unitsCoeHom u, by rw [dyadicSquareClassHom_unitsCoeHom, hu]⟩
  · refine ⟨pUnit 2 * unitsCoeHom u, ?_⟩
    rw [map_mul, dyadicSquareClassHom_pUnit, dyadicSquareClassHom_unitsCoeHom, hu,
      Prod.mk_mul_mk, mul_one, one_mul]

/-- **The square classes of the dyadic field.** The square-class group is the elementary
abelian group of order eight: the parity of the valuation and the residue modulo eight of
the unit part are independent invariants.

This is Serre, *A Course in Arithmetic*, Ch. II §3.3, Theorem 4 [@Ser73, p. 17]. -/
noncomputable def dyadicSquareClassEquiv :
    PadicSquareClass 2 ≃* Multiplicative (ZMod 2) × (ZMod 8)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq ker_dyadicSquareClassHom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ dyadicSquareClassHom_surjective)

/-- The square-class group of the dyadic field has order eight. -/
theorem card_squareClass_two : Nat.card (PadicSquareClass 2) = 8 := by
  rw [Nat.card_congr dyadicSquareClassEquiv.toEquiv, Nat.card_prod,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2), Nat.card_zmod,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  decide

/-! ## The square-class coordinates -/

/-- The square-class coordinates of a nonzero dyadic number: the parity of the valuation
and the residue modulo eight of the unit part. -/
noncomputable def dyadicCoord (x : ℚ_[2]ˣ) : ZMod 2 × ZMod 8 :=
  ((((x : ℚ_[2]).valuation : ZMod 2)), ((dyadicResidue x : (ZMod 8)ˣ) : ZMod 8))

/-- The residue coordinate of a nonzero dyadic number is invertible. -/
theorem isUnit_dyadicCoord_snd (x : ℚ_[2]ˣ) : IsUnit (dyadicCoord x).2 :=
  (dyadicResidue x).isUnit

theorem dyadicCoord_mul (x y : ℚ_[2]ˣ) :
    dyadicCoord (x * y) =
      ((dyadicCoord x).1 + (dyadicCoord y).1, (dyadicCoord x).2 * (dyadicCoord y).2) := by
  refine Prod.ext ?_ ?_
  · change (((x * y : ℚ_[2]ˣ) : ℚ_[2]).valuation : ZMod 2) = _
    rw [Units.val_mul, Padic.valuation_mul (Units.ne_zero x) (Units.ne_zero y), Int.cast_add]
    rfl
  · change ((dyadicResidue (x * y) : (ZMod 8)ˣ) : ZMod 8) = _
    rw [map_mul, Units.val_mul]
    rfl

/-- The square-class coordinates determine the square class. -/
theorem exists_sq_of_dyadicCoord_eq {x y : ℚ_[2]ˣ} (h : dyadicCoord x = dyadicCoord y) :
    ∃ s : ℚ_[2]ˣ, x = y * s ^ 2 := by
  refine exists_sq_of_dyadicSquareClassHom_eq (Prod.ext ?_ ?_)
  · rw [dyadicSquareClassHom_apply, dyadicSquareClassHom_apply, valuationModTwo_apply,
      valuationModTwo_apply]
    exact congrArg Multiplicative.ofAdd (congrArg Prod.fst h)
  · exact Units.ext (congrArg Prod.snd h)

/-! ## The closed formula for the dyadic Hilbert symbol -/

/-- The parity of `(u - 1) / 2`, as a function of the residue modulo eight. -/
def dyadicEps (u : ZMod 8) : ZMod 2 := if u = 3 ∨ u = 7 then 1 else 0

/-- The parity of `(u ^ 2 - 1) / 8`, as a function of the residue modulo eight. -/
def dyadicOmega (u : ZMod 8) : ZMod 2 := if u = 3 ∨ u = 5 then 1 else 0

/-- The exponent of the closed formula, as a function of the square-class coordinates. -/
def dyadicPairing (c d : ZMod 2 × ZMod 8) : ZMod 2 :=
  dyadicEps c.2 * dyadicEps d.2 + c.1 * dyadicOmega d.2 + d.1 * dyadicOmega c.2

/-- Both residue characters are additive on invertible residues. -/
theorem dyadicEps_mul {u v : ZMod 8} (hu : IsUnit u) (hv : IsUnit v) :
    dyadicEps (u * v) = dyadicEps u + dyadicEps v := by
  obtain ⟨a, ha⟩ := isUnit_iff_exists_inv.mp hu
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hv
  revert ha hb
  revert u v a b
  decide

theorem dyadicOmega_mul {u v : ZMod 8} (hu : IsUnit u) (hv : IsUnit v) :
    dyadicOmega (u * v) = dyadicOmega u + dyadicOmega v := by
  obtain ⟨a, ha⟩ := isUnit_iff_exists_inv.mp hu
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hv
  revert ha hb
  revert u v a b
  decide

/-- The exponent is additive in its second entry, on square-class coordinates of nonzero
dyadic numbers. -/
theorem dyadicPairing_mul (x y z : ℚ_[2]ˣ) :
    dyadicPairing (dyadicCoord x) (dyadicCoord (y * z)) =
      dyadicPairing (dyadicCoord x) (dyadicCoord y) +
        dyadicPairing (dyadicCoord x) (dyadicCoord z) := by
  rw [dyadicPairing, dyadicPairing, dyadicPairing, dyadicCoord_mul,
    dyadicEps_mul (isUnit_dyadicCoord_snd y) (isUnit_dyadicCoord_snd z),
    dyadicOmega_mul (isUnit_dyadicCoord_snd y) (isUnit_dyadicCoord_snd z)]
  ring

/-! ## The eight representatives and their coordinates -/

/-- Minus one, as a nonzero dyadic number. -/
noncomputable def negOne : ℚ_[2]ˣ := unitsCoeHom (-1)

/-- Five, as a nonzero dyadic number. -/
noncomputable def five : ℚ_[2]ˣ := unitsCoeHom fiveUnit

@[simp]
theorem coe_negOne : ((negOne : ℚ_[2]ˣ) : ℚ_[2]) = -1 := by
  rw [negOne, coe_unitsCoeHom, Units.val_neg, Units.val_one]
  push_cast
  ring

@[simp]
theorem coe_five : ((five : ℚ_[2]ˣ) : ℚ_[2]) = 5 := by
  rw [five, coe_unitsCoeHom, coe_fiveUnit]
  norm_cast

@[simp]
theorem dyadicResidue_unitsCoeHom (u : ℤ_[2]ˣ) :
    dyadicResidue (unitsCoeHom u) = dyadicUnitClass u :=
  congrArg Prod.snd (dyadicSquareClassHom_unitsCoeHom u)

theorem dyadicCoord_unitsCoeHom (u : ℤ_[2]ˣ) :
    dyadicCoord (unitsCoeHom u) = (0, ((dyadicUnitClass u : (ZMod 8)ˣ) : ZMod 8)) := by
  refine Prod.ext ?_ ?_
  · change ((((unitsCoeHom u : ℚ_[2]ˣ) : ℚ_[2]).valuation : ZMod 2)) = 0
    rw [valuation_unitsCoeHom]
    rfl
  · change ((dyadicResidue (unitsCoeHom u) : (ZMod 8)ˣ) : ZMod 8) = _
    rw [dyadicResidue_unitsCoeHom]

@[simp]
theorem dyadicCoord_one : dyadicCoord (1 : ℚ_[2]ˣ) = (0, 1) := by
  refine Prod.ext ?_ ?_
  · change ((((1 : ℚ_[2]ˣ) : ℚ_[2]).valuation : ZMod 2)) = 0
    rw [Units.val_one, Padic.valuation_one]
    rfl
  · change ((dyadicResidue 1 : (ZMod 8)ˣ) : ZMod 8) = 1
    rw [map_one, Units.val_one]

@[simp]
theorem dyadicCoord_negOne : dyadicCoord negOne = (0, 7) := by
  rw [negOne, dyadicCoord_unitsCoeHom, coe_dyadicUnitClass_neg, coe_dyadicUnitClass_one]
  decide

@[simp]
theorem dyadicCoord_five : dyadicCoord five = (0, 5) := by
  rw [five, dyadicCoord_unitsCoeHom, coe_dyadicUnitClass_fiveUnit]

@[simp]
theorem dyadicCoord_two : dyadicCoord (pUnit 2) = (1, 1) := by
  refine Prod.ext ?_ ?_
  · change ((((pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]).valuation : ZMod 2)) = 1
    rw [coe_pUnit, Padic.valuation_p]
    rfl
  · change ((dyadicResidue (pUnit 2) : (ZMod 8)ˣ) : ZMod 8) = 1
    rw [show dyadicResidue (pUnit 2) = 1 from congrArg Prod.snd dyadicSquareClassHom_pUnit,
      Units.val_one]

/-! ## Reduction of the symbol along square classes -/

/-- The symbol is unchanged when the second entry moves inside its square class. -/
theorem hilbertSymbol_eq_one_of_dyadicCoord_eq {r g y : ℚ_[2]ˣ}
    (h : hilbertSymbol (r : ℚ_[2]) (g : ℚ_[2]) = 1) (hy : dyadicCoord y = dyadicCoord g) :
    hilbertSymbol (r : ℚ_[2]) (y : ℚ_[2]) = 1 := by
  obtain ⟨s, rfl⟩ := exists_sq_of_dyadicCoord_eq hy
  rw [Units.val_mul, Units.val_pow_eq_pow_val,
    hilbertSymbol_mul_square_right _ _ (Units.ne_zero s)]
  exact h

/-- The symbol is unchanged when the first entry moves inside its square class. -/
theorem hilbertSymbol_congr_left {x r : ℚ_[2]ˣ} (h : dyadicCoord x = dyadicCoord r)
    (y : ℚ_[2]ˣ) :
    hilbertSymbol (x : ℚ_[2]) (y : ℚ_[2]) = hilbertSymbol (r : ℚ_[2]) (y : ℚ_[2]) := by
  obtain ⟨s, rfl⟩ := exists_sq_of_dyadicCoord_eq h
  rw [Units.val_mul, Units.val_pow_eq_pow_val,
    hilbertSymbol_mul_square_left _ _ (Units.ne_zero s)]

/-- Norms from a fixed quadratic extension are closed under multiplication, so a symbol
that is one on two elements is one on their product. -/
theorem hilbertSymbol_mul_eq_one {r g₁ g₂ : ℚ_[2]ˣ}
    (h₁ : hilbertSymbol (r : ℚ_[2]) (g₁ : ℚ_[2]) = 1)
    (h₂ : hilbertSymbol (r : ℚ_[2]) (g₂ : ℚ_[2]) = 1) :
    hilbertSymbol (r : ℚ_[2]) ((g₁ * g₂ : ℚ_[2]ˣ) : ℚ_[2]) = 1 := by
  rw [Units.val_mul]
  refine hilbertSymbol_eq_one_of_isNormFromSqrt (Units.ne_zero r)
    (mul_ne_zero (Units.ne_zero g₁) (Units.ne_zero g₂)) ?_
  exact ((hilbertSymbol_eq_one_iff_isNormFromSqrt (Units.ne_zero r) (Units.ne_zero g₁)).mp
    h₁).mul ((hilbertSymbol_eq_one_iff_isNormFromSqrt (Units.ne_zero r)
      (Units.ne_zero g₂)).mp h₂)

/-! ## The five basic norm relations -/

/-- Minus seven is a dyadic square, since it is congruent to one modulo eight. -/
theorem isSquare_neg_seven : IsSquare (-7 : ℤ_[2]) := by
  refine isSquare_of_toZModPow_three_eq_one ?_
  have h : ((7 : ℕ) : ℤ_[2]) = 7 := by norm_cast
  rw [show (-7 : ℤ_[2]) = -((7 : ℕ) : ℤ_[2]) by rw [h], map_neg, map_natCast]
  decide

/-- Minus fifteen is a dyadic square, since it is congruent to one modulo eight. -/
theorem isSquare_neg_fifteen : IsSquare (-15 : ℤ_[2]) := by
  refine isSquare_of_toZModPow_three_eq_one ?_
  have h : ((15 : ℕ) : ℤ_[2]) = 15 := by norm_cast
  rw [show (-15 : ℤ_[2]) = -((15 : ℕ) : ℤ_[2]) by rw [h], map_neg, map_natCast]
  decide

/-- `2 = 1 ² + 1 ²` is a norm from the Gaussian dyadic extension. -/
theorem hilbertSymbol_negOne_two :
    hilbertSymbol ((negOne : ℚ_[2]ˣ) : ℚ_[2]) ((pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]) = 1 := by
  refine hilbertSymbol_eq_one_of_isNormFromSqrt (Units.ne_zero _) (Units.ne_zero _) ⟨1, 1, ?_⟩
  rw [coe_negOne, coe_pUnit]
  push_cast
  ring

/-- `5 = 1 ² + 2 ²` is a norm from the Gaussian dyadic extension. -/
theorem hilbertSymbol_negOne_five :
    hilbertSymbol ((negOne : ℚ_[2]ˣ) : ℚ_[2]) ((five : ℚ_[2]ˣ) : ℚ_[2]) = 1 := by
  refine hilbertSymbol_eq_one_of_isNormFromSqrt (Units.ne_zero _) (Units.ne_zero _) ⟨1, 2, ?_⟩
  rw [coe_negOne, coe_five]
  ring

/-- `-2 = (√-7) ² + 5 · 1 ²` is a norm from the extension by `√-5`. -/
theorem hilbertSymbol_negFive_negTwo :
    hilbertSymbol ((negOne * five : ℚ_[2]ˣ) : ℚ_[2])
      ((negOne * pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]) = 1 := by
  obtain ⟨s, hs⟩ := isSquare_neg_seven
  have hval : ((s : ℤ_[2]) : ℚ_[2]) * ((s : ℤ_[2]) : ℚ_[2]) = -7 := by
    rw [← PadicInt.coe_mul, ← hs]
    norm_cast
  refine hilbertSymbol_eq_one_of_isNormFromSqrt (Units.ne_zero _) (Units.ne_zero _)
    ⟨((s : ℤ_[2]) : ℚ_[2]), 1, ?_⟩
  rw [Units.val_mul, Units.val_mul, coe_negOne, coe_five, coe_pUnit, hval]
  push_cast
  ring

/-- `-1 = 3 ² - 10 · 1 ²` is a norm from the extension by `√10`. -/
theorem hilbertSymbol_ten_negOne :
    hilbertSymbol ((five * pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]) ((negOne : ℚ_[2]ˣ) : ℚ_[2]) = 1 := by
  refine hilbertSymbol_eq_one_of_isNormFromSqrt (Units.ne_zero _) (Units.ne_zero _) ⟨3, 1, ?_⟩
  rw [Units.val_mul, coe_negOne, coe_five, coe_pUnit]
  push_cast
  ring

/-- `-5 = (√-15) ² + 10 · 1 ²` is a norm from the extension by `√-10`. -/
theorem hilbertSymbol_negTen_negFive :
    hilbertSymbol ((negOne * five * pUnit 2 : ℚ_[2]ˣ) : ℚ_[2])
      ((negOne * five : ℚ_[2]ˣ) : ℚ_[2]) = 1 := by
  obtain ⟨s, hs⟩ := isSquare_neg_fifteen
  have hval : ((s : ℤ_[2]) : ℚ_[2]) * ((s : ℤ_[2]) : ℚ_[2]) = -15 := by
    rw [← PadicInt.coe_mul, ← hs]
    norm_cast
  refine hilbertSymbol_eq_one_of_isNormFromSqrt (Units.ne_zero _) (Units.ne_zero _)
    ⟨((s : ℤ_[2]) : ℚ_[2]), 1, ?_⟩
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_negOne, coe_five, coe_pUnit, hval]
  push_cast
  ring

/-! ## The symbol against each representative -/

@[simp]
theorem dyadicCoord_negFive : dyadicCoord (negOne * five) = (0, 3) := by
  rw [dyadicCoord_mul, dyadicCoord_negOne, dyadicCoord_five]
  decide

@[simp]
theorem dyadicCoord_negTwo : dyadicCoord (negOne * pUnit 2) = (1, 7) := by
  rw [dyadicCoord_mul, dyadicCoord_negOne, dyadicCoord_two]
  decide

@[simp]
theorem dyadicCoord_ten : dyadicCoord (five * pUnit 2) = (1, 5) := by
  rw [dyadicCoord_mul, dyadicCoord_five, dyadicCoord_two]
  decide

@[simp]
theorem dyadicCoord_negTen : dyadicCoord (negOne * five * pUnit 2) = (1, 3) := by
  rw [dyadicCoord_mul, dyadicCoord_negFive, dyadicCoord_two]
  decide

/-- The symbol of a nonzero dyadic number against one is one. -/
theorem hilbertSymbol_one_unit (r : ℚ_[2]ˣ) :
    hilbertSymbol (r : ℚ_[2]) ((1 : ℚ_[2]ˣ) : ℚ_[2]) = 1 := by
  rw [Units.val_one]
  exact hilbertSymbol_one_right _ (Units.ne_zero r)

/-- The residue coordinate of a nonzero dyadic number has an inverse. -/
theorem exists_inv_dyadicCoord_snd (y : ℚ_[2]ˣ) : ∃ e, (dyadicCoord y).2 * e = 1 :=
  isUnit_iff_exists_inv.mp (isUnit_dyadicCoord_snd y)

/-- Against `-1` the symbol is one exactly on the classes of `1`, `2`, `5` and `10`. -/
theorem hilbertSymbol_negOne_of_pairing_eq_zero (y : ℚ_[2]ˣ)
    (h : dyadicPairing (dyadicCoord negOne) (dyadicCoord y) = 0) :
    hilbertSymbol ((negOne : ℚ_[2]ˣ) : ℚ_[2]) (y : ℚ_[2]) = 1 := by
  rw [dyadicCoord_negOne] at h
  have hcases : ∀ d : ZMod 2 × ZMod 8, (∃ e, d.2 * e = 1) → dyadicPairing (0, 7) d = 0 →
      d = (0, 1) ∨ d = (1, 1) ∨ d = (0, 5) ∨ d = (1, 5) := by decide
  rcases hcases (dyadicCoord y) (exists_inv_dyadicCoord_snd y) h with hy | hy | hy | hy
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq (hilbertSymbol_one_unit _)
      (by rw [hy, dyadicCoord_one])
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq hilbertSymbol_negOne_two
      (by rw [hy, dyadicCoord_two])
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq hilbertSymbol_negOne_five
      (by rw [hy, dyadicCoord_five])
  · refine hilbertSymbol_eq_one_of_dyadicCoord_eq
      (hilbertSymbol_mul_eq_one hilbertSymbol_negOne_two hilbertSymbol_negOne_five) ?_
    rw [hy, dyadicCoord_mul, dyadicCoord_two, dyadicCoord_five]
    decide

/-- The symbol of a nonzero dyadic number against its negative is one. -/
theorem hilbertSymbol_neg_eq_one {r g : ℚ_[2]ˣ} (h : (g : ℚ_[2]) = -(r : ℚ_[2])) :
    hilbertSymbol (r : ℚ_[2]) (g : ℚ_[2]) = 1 := by
  rw [h]
  exact hilbertSymbol_neg_self _ (Units.ne_zero r)

/-- Against `5` the symbol is one exactly on the classes of even valuation. -/
theorem hilbertSymbol_five_of_pairing_eq_zero (y : ℚ_[2]ˣ)
    (h : dyadicPairing (dyadicCoord five) (dyadicCoord y) = 0) :
    hilbertSymbol ((five : ℚ_[2]ˣ) : ℚ_[2]) (y : ℚ_[2]) = 1 := by
  have h₁ : hilbertSymbol ((five : ℚ_[2]ˣ) : ℚ_[2]) ((negOne : ℚ_[2]ˣ) : ℚ_[2]) = 1 := by
    rw [hilbertSymbol_comm]
    exact hilbertSymbol_negOne_five
  have h₂ : hilbertSymbol ((five : ℚ_[2]ˣ) : ℚ_[2]) ((negOne * five : ℚ_[2]ˣ) : ℚ_[2]) = 1 :=
    hilbertSymbol_neg_eq_one (by rw [Units.val_mul, coe_negOne]; ring)
  rw [dyadicCoord_five] at h
  have hcases : ∀ d : ZMod 2 × ZMod 8, (∃ e, d.2 * e = 1) → dyadicPairing (0, 5) d = 0 →
      d = (0, 1) ∨ d = (0, 7) ∨ d = (0, 3) ∨ d = (0, 5) := by decide
  rcases hcases (dyadicCoord y) (exists_inv_dyadicCoord_snd y) h with hy | hy | hy | hy
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq (hilbertSymbol_one_unit _)
      (by rw [hy, dyadicCoord_one])
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq h₁ (by rw [hy, dyadicCoord_negOne])
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq h₂ (by rw [hy, dyadicCoord_negFive])
  · refine hilbertSymbol_eq_one_of_dyadicCoord_eq (hilbertSymbol_mul_eq_one h₁ h₂) ?_
    rw [hy, dyadicCoord_mul, dyadicCoord_negOne, dyadicCoord_negFive]
    decide

/-- Against `-5` the symbol is one exactly on the classes of `1`, `5`, `-2` and `-10`. -/
theorem hilbertSymbol_negFive_of_pairing_eq_zero (y : ℚ_[2]ˣ)
    (h : dyadicPairing (dyadicCoord (negOne * five)) (dyadicCoord y) = 0) :
    hilbertSymbol ((negOne * five : ℚ_[2]ˣ) : ℚ_[2]) (y : ℚ_[2]) = 1 := by
  have h₁ : hilbertSymbol ((negOne * five : ℚ_[2]ˣ) : ℚ_[2]) ((five : ℚ_[2]ˣ) : ℚ_[2]) = 1 := by
    rw [hilbertSymbol_comm]
    exact hilbertSymbol_neg_eq_one (by rw [Units.val_mul, coe_negOne]; ring)
  have h₂ := hilbertSymbol_negFive_negTwo
  rw [dyadicCoord_negFive] at h
  have hcases : ∀ d : ZMod 2 × ZMod 8, (∃ e, d.2 * e = 1) → dyadicPairing (0, 3) d = 0 →
      d = (0, 1) ∨ d = (0, 5) ∨ d = (1, 7) ∨ d = (1, 3) := by decide
  rcases hcases (dyadicCoord y) (exists_inv_dyadicCoord_snd y) h with hy | hy | hy | hy
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq (hilbertSymbol_one_unit _)
      (by rw [hy, dyadicCoord_one])
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq h₁ (by rw [hy, dyadicCoord_five])
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq h₂ (by rw [hy, dyadicCoord_negTwo])
  · refine hilbertSymbol_eq_one_of_dyadicCoord_eq (hilbertSymbol_mul_eq_one h₁ h₂) ?_
    rw [hy, dyadicCoord_mul, dyadicCoord_five, dyadicCoord_negTwo]
    decide

/-- Against `2` the symbol is one exactly on the classes of `1`, `2`, `-1` and `-2`. -/
theorem hilbertSymbol_two_of_pairing_eq_zero (y : ℚ_[2]ˣ)
    (h : dyadicPairing (dyadicCoord (pUnit 2)) (dyadicCoord y) = 0) :
    hilbertSymbol ((pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]) (y : ℚ_[2]) = 1 := by
  have h₁ : hilbertSymbol ((pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]) ((negOne : ℚ_[2]ˣ) : ℚ_[2]) = 1 := by
    rw [hilbertSymbol_comm]
    exact hilbertSymbol_negOne_two
  have h₂ : hilbertSymbol ((pUnit 2 : ℚ_[2]ˣ) : ℚ_[2])
      ((negOne * pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]) = 1 :=
    hilbertSymbol_neg_eq_one (by rw [Units.val_mul, coe_negOne]; ring)
  rw [dyadicCoord_two] at h
  have hcases : ∀ d : ZMod 2 × ZMod 8, (∃ e, d.2 * e = 1) → dyadicPairing (1, 1) d = 0 →
      d = (0, 1) ∨ d = (0, 7) ∨ d = (1, 7) ∨ d = (1, 1) := by decide
  rcases hcases (dyadicCoord y) (exists_inv_dyadicCoord_snd y) h with hy | hy | hy | hy
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq (hilbertSymbol_one_unit _)
      (by rw [hy, dyadicCoord_one])
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq h₁ (by rw [hy, dyadicCoord_negOne])
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq h₂ (by rw [hy, dyadicCoord_negTwo])
  · refine hilbertSymbol_eq_one_of_dyadicCoord_eq (hilbertSymbol_mul_eq_one h₁ h₂) ?_
    rw [hy, dyadicCoord_mul, dyadicCoord_negOne, dyadicCoord_negTwo]
    decide

/-- Against `-2` the symbol is one exactly on the classes of `1`, `2`, `-5` and `-10`. -/
theorem hilbertSymbol_negTwo_of_pairing_eq_zero (y : ℚ_[2]ˣ)
    (h : dyadicPairing (dyadicCoord (negOne * pUnit 2)) (dyadicCoord y) = 0) :
    hilbertSymbol ((negOne * pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]) (y : ℚ_[2]) = 1 := by
  have h₁ : hilbertSymbol ((negOne * pUnit 2 : ℚ_[2]ˣ) : ℚ_[2])
      ((pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]) = 1 := by
    rw [hilbertSymbol_comm]
    exact hilbertSymbol_neg_eq_one (by rw [Units.val_mul, coe_negOne]; ring)
  have h₂ : hilbertSymbol ((negOne * pUnit 2 : ℚ_[2]ˣ) : ℚ_[2])
      ((negOne * five : ℚ_[2]ˣ) : ℚ_[2]) = 1 := by
    rw [hilbertSymbol_comm]
    exact hilbertSymbol_negFive_negTwo
  rw [dyadicCoord_negTwo] at h
  have hcases : ∀ d : ZMod 2 × ZMod 8, (∃ e, d.2 * e = 1) → dyadicPairing (1, 7) d = 0 →
      d = (0, 1) ∨ d = (1, 1) ∨ d = (0, 3) ∨ d = (1, 3) := by decide
  rcases hcases (dyadicCoord y) (exists_inv_dyadicCoord_snd y) h with hy | hy | hy | hy
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq (hilbertSymbol_one_unit _)
      (by rw [hy, dyadicCoord_one])
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq h₁ (by rw [hy, dyadicCoord_two])
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq h₂ (by rw [hy, dyadicCoord_negFive])
  · refine hilbertSymbol_eq_one_of_dyadicCoord_eq (hilbertSymbol_mul_eq_one h₁ h₂) ?_
    rw [hy, dyadicCoord_mul, dyadicCoord_two, dyadicCoord_negFive]
    decide

/-- Against `10` the symbol is one exactly on the classes of `1`, `-1`, `10` and `-10`. -/
theorem hilbertSymbol_ten_of_pairing_eq_zero (y : ℚ_[2]ˣ)
    (h : dyadicPairing (dyadicCoord (five * pUnit 2)) (dyadicCoord y) = 0) :
    hilbertSymbol ((five * pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]) (y : ℚ_[2]) = 1 := by
  have h₁ := hilbertSymbol_ten_negOne
  have h₂ : hilbertSymbol ((five * pUnit 2 : ℚ_[2]ˣ) : ℚ_[2])
      ((negOne * (five * pUnit 2) : ℚ_[2]ˣ) : ℚ_[2]) = 1 :=
    hilbertSymbol_neg_eq_one (by rw [Units.val_mul, coe_negOne]; ring)
  rw [dyadicCoord_ten] at h
  have hcases : ∀ d : ZMod 2 × ZMod 8, (∃ e, d.2 * e = 1) → dyadicPairing (1, 5) d = 0 →
      d = (0, 1) ∨ d = (0, 7) ∨ d = (1, 3) ∨ d = (1, 5) := by decide
  rcases hcases (dyadicCoord y) (exists_inv_dyadicCoord_snd y) h with hy | hy | hy | hy
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq (hilbertSymbol_one_unit _)
      (by rw [hy, dyadicCoord_one])
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq h₁ (by rw [hy, dyadicCoord_negOne])
  · refine hilbertSymbol_eq_one_of_dyadicCoord_eq h₂ ?_
    rw [hy, dyadicCoord_mul, dyadicCoord_negOne, dyadicCoord_ten]
    decide
  · refine hilbertSymbol_eq_one_of_dyadicCoord_eq (hilbertSymbol_mul_eq_one h₁ h₂) ?_
    rw [hy, dyadicCoord_mul, dyadicCoord_negOne, dyadicCoord_mul, dyadicCoord_negOne,
      dyadicCoord_ten]
    decide

/-- Against `-10` the symbol is one exactly on the classes of `1`, `-5`, `10` and `-2`. -/
theorem hilbertSymbol_negTen_of_pairing_eq_zero (y : ℚ_[2]ˣ)
    (h : dyadicPairing (dyadicCoord (negOne * five * pUnit 2)) (dyadicCoord y) = 0) :
    hilbertSymbol ((negOne * five * pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]) (y : ℚ_[2]) = 1 := by
  have h₁ := hilbertSymbol_negTen_negFive
  have hval : ((five * pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]) =
      -((negOne * five * pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]) := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_negOne]
    ring
  have h₂ : hilbertSymbol ((negOne * five * pUnit 2 : ℚ_[2]ˣ) : ℚ_[2])
      ((five * pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]) = 1 := hilbertSymbol_neg_eq_one hval
  rw [dyadicCoord_negTen] at h
  have hcases : ∀ d : ZMod 2 × ZMod 8, (∃ e, d.2 * e = 1) → dyadicPairing (1, 3) d = 0 →
      d = (0, 1) ∨ d = (0, 3) ∨ d = (1, 5) ∨ d = (1, 7) := by decide
  rcases hcases (dyadicCoord y) (exists_inv_dyadicCoord_snd y) h with hy | hy | hy | hy
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq (hilbertSymbol_one_unit _)
      (by rw [hy, dyadicCoord_one])
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq h₁ (by rw [hy, dyadicCoord_negFive])
  · exact hilbertSymbol_eq_one_of_dyadicCoord_eq h₂ (by rw [hy, dyadicCoord_ten])
  · refine hilbertSymbol_eq_one_of_dyadicCoord_eq (hilbertSymbol_mul_eq_one h₁ h₂) ?_
    rw [hy, dyadicCoord_mul, dyadicCoord_negFive, dyadicCoord_ten]
    decide

/-! ## The dyadic symbol is bilinear -/

/-- **The vanishing of the exponent forces the symbol to be one.** Every square class is
represented by one of `±1`, `±5`, `±2`, `±10`, and against each representative the classes
with vanishing exponent are the products of two classes that are norms. -/
theorem hilbertSymbol_eq_one_of_dyadicPairing_eq_zero (x y : ℚ_[2]ˣ)
    (h : dyadicPairing (dyadicCoord x) (dyadicCoord y) = 0) :
    hilbertSymbol (x : ℚ_[2]) (y : ℚ_[2]) = 1 := by
  have hcases : ∀ c : ZMod 2 × ZMod 8, (∃ e, c.2 * e = 1) →
      c = (0, 1) ∨ c = (0, 7) ∨ c = (0, 5) ∨ c = (0, 3) ∨
        c = (1, 1) ∨ c = (1, 7) ∨ c = (1, 5) ∨ c = (1, 3) := by decide
  rcases hcases (dyadicCoord x) (exists_inv_dyadicCoord_snd x) with
    hx | hx | hx | hx | hx | hx | hx | hx
  · have hxr : dyadicCoord x = dyadicCoord (1 : ℚ_[2]ˣ) := by rw [hx, dyadicCoord_one]
    rw [hilbertSymbol_congr_left hxr y, Units.val_one]
    exact hilbertSymbol_one_left _ (Units.ne_zero y)
  · have hxr : dyadicCoord x = dyadicCoord negOne := by rw [hx, dyadicCoord_negOne]
    rw [hxr] at h
    rw [hilbertSymbol_congr_left hxr y]
    exact hilbertSymbol_negOne_of_pairing_eq_zero y h
  · have hxr : dyadicCoord x = dyadicCoord five := by rw [hx, dyadicCoord_five]
    rw [hxr] at h
    rw [hilbertSymbol_congr_left hxr y]
    exact hilbertSymbol_five_of_pairing_eq_zero y h
  · have hxr : dyadicCoord x = dyadicCoord (negOne * five) := by rw [hx, dyadicCoord_negFive]
    rw [hxr] at h
    rw [hilbertSymbol_congr_left hxr y]
    exact hilbertSymbol_negFive_of_pairing_eq_zero y h
  · have hxr : dyadicCoord x = dyadicCoord (pUnit 2) := by rw [hx, dyadicCoord_two]
    rw [hxr] at h
    rw [hilbertSymbol_congr_left hxr y]
    exact hilbertSymbol_two_of_pairing_eq_zero y h
  · have hxr : dyadicCoord x = dyadicCoord (negOne * pUnit 2) := by
      rw [hx, dyadicCoord_negTwo]
    rw [hxr] at h
    rw [hilbertSymbol_congr_left hxr y]
    exact hilbertSymbol_negTwo_of_pairing_eq_zero y h
  · have hxr : dyadicCoord x = dyadicCoord (five * pUnit 2) := by rw [hx, dyadicCoord_ten]
    rw [hxr] at h
    rw [hilbertSymbol_congr_left hxr y]
    exact hilbertSymbol_ten_of_pairing_eq_zero y h
  · have hxr : dyadicCoord x = dyadicCoord (negOne * five * pUnit 2) := by
      rw [hx, dyadicCoord_negTen]
    rw [hxr] at h
    rw [hilbertSymbol_congr_left hxr y]
    exact hilbertSymbol_negTen_of_pairing_eq_zero y h

/-- **The dyadic Hilbert symbol is multiplicative in its first entry, on nonzero
arguments.** Two entries with symbol `-1` have exponent one against the second entry, so
their product has exponent zero and symbol one. -/
theorem hilbertSymbol_mul_left_units (A B C : ℚ_[2]ˣ) :
    hilbertSymbol ((A * B : ℚ_[2]ˣ) : ℚ_[2]) (C : ℚ_[2]) =
      hilbertSymbol (A : ℚ_[2]) (C : ℚ_[2]) * hilbertSymbol (B : ℚ_[2]) (C : ℚ_[2]) := by
  have step : ∀ x : ℚ_[2]ˣ, hilbertSymbol (x : ℚ_[2]) (C : ℚ_[2]) ≠ 1 →
      dyadicPairing (dyadicCoord C) (dyadicCoord x) = 1 := by
    intro x hx
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1)
      (dyadicPairing (dyadicCoord C) (dyadicCoord x)) with hz | hz
    · refine absurd ?_ hx
      rw [hilbertSymbol_comm]
      exact hilbertSymbol_eq_one_of_dyadicPairing_eq_zero C x hz
    · exact hz
  by_cases hac : hilbertSymbol (A : ℚ_[2]) (C : ℚ_[2]) = 1
  · rw [Units.val_mul]
    exact hilbertSymbol_mul_left_of_eq_one (Units.ne_zero A) (Units.ne_zero B)
      (Units.ne_zero C) hac
  by_cases hbc : hilbertSymbol (B : ℚ_[2]) (C : ℚ_[2]) = 1
  · rw [Units.val_mul, mul_comm (A : ℚ_[2]),
      hilbertSymbol_mul_left_of_eq_one (Units.ne_zero B) (Units.ne_zero A)
        (Units.ne_zero C) hbc, mul_comm]
  have hAB : dyadicPairing (dyadicCoord C) (dyadicCoord (A * B)) = 0 := by
    rw [dyadicPairing_mul, step A hac, step B hbc]
    decide
  have hkey : hilbertSymbol ((A * B : ℚ_[2]ˣ) : ℚ_[2]) (C : ℚ_[2]) = 1 := by
    rw [hilbertSymbol_comm]
    exact hilbertSymbol_eq_one_of_dyadicPairing_eq_zero C (A * B) hAB
  rw [hkey, (hilbertSymbol_eq_one_or_neg_one (Units.ne_zero A) (Units.ne_zero C)).resolve_left
      hac,
    (hilbertSymbol_eq_one_or_neg_one (Units.ne_zero B) (Units.ne_zero C)).resolve_left hbc]
  norm_num

/-- **The dyadic Hilbert symbol is bilinear.** -/
instance instHasBilinearHilbertSymbolTwo : HasBilinearHilbertSymbol ℚ_[2] where
  map_mul_left {a b c} := by
    by_cases h0 : a = 0 ∨ b = 0 ∨ c = 0
    · rcases h0 with h0 | h0 | h0 <;> simp [hilbertSymbol, h0]
    push Not at h0
    obtain ⟨ha, hb, hc⟩ := h0
    simpa using hilbertSymbol_mul_left_units (Units.mk0 a ha) (Units.mk0 b hb)
      (Units.mk0 c hc)

/-! ## Two anisotropic ternary forms -/

/-- Two is nonzero in the dyadic integers. -/
theorem two_ne_zero_padicIntTwo : (2 : ℤ_[2]) ≠ 0 := by
  intro h
  have hnorm := norm_two_padicIntTwo
  rw [h, norm_zero] at hnorm
  norm_num at hnorm

/-- The residue of four modulo eight. -/
theorem toZModPow_three_four : toZModPow 3 (4 : ℤ_[2]) = 4 := by
  have h : ((4 : ℕ) : ℤ_[2]) = 4 := by norm_cast
  rw [← h, map_natCast]
  decide

/-- The residue of five modulo two. -/
theorem toZMod_five : toZMod (5 : ℤ_[2]) = 1 := by
  have h : ((5 : ℕ) : ℤ_[2]) = 5 := by norm_cast
  rw [← h, map_natCast]
  decide

/-- The residue of two modulo two. -/
theorem toZMod_two : toZMod (2 : ℤ_[2]) = 0 := by
  have h : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_cast
  rw [← h, map_natCast]
  decide

/-- A dyadic integer of norm less than one has vanishing residue. -/
theorem toZMod_eq_zero_of_norm_lt_one {w : ℤ_[2]} (hw : ‖w‖ < 1) : toZMod w = 0 := by
  by_contra hne
  exact absurd (norm_eq_one_of_toZMod_ne_zero hne) (ne_of_lt hw)

/-- The square of a dyadic unit is congruent to one modulo eight. -/
theorem toZModPow_three_mul_self {w : ℤ_[2]} (hw : ‖w‖ = 1) : toZModPow 3 (w * w) = 1 := by
  refine toZModPow_three_eq_one_of_isSquare ?_ ⟨w, rfl⟩
  rw [norm_mul, hw, one_mul]

/-- A dyadic integer congruent to four modulo eight is four times a unit. -/
theorem eq_four_mul_unit {z : ℤ_[2]} (h : toZModPow 3 z = 4) :
    ∃ m : ℤ_[2], ‖m‖ = 1 ∧ z = 4 * m := by
  have hmem : z - 4 ∈ RingHom.ker (toZModPow (p := 2) 3) := by
    rw [RingHom.mem_ker, map_sub, h, toZModPow_three_four, sub_self]
  rw [ker_toZModPow] at hmem
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hmem
  refine ⟨1 + 2 * t, ?_, ?_⟩
  · refine norm_eq_one_of_toZMod_ne_zero ?_
    rw [map_add, map_one, map_mul, toZMod_two, zero_mul, add_zero]
    exact one_ne_zero
  · have h8 : ((2 : ℕ) : ℤ_[2]) ^ 3 = 8 := by
      push_cast
      norm_num
    rw [h8] at ht
    linear_combination ht

/-- Away from the unramified extension the norm form is a square times a unit: `w ² - 5`
is a unit when `w` is not, and four times a unit when `w` is. -/
theorem exists_unit_mul_self_sub_five (w : ℤ_[2]) :
    ∃ t m : ℤ_[2], t ≠ 0 ∧ ‖m‖ = 1 ∧ w * w - 5 = t * t * m := by
  rcases eq_or_lt_of_le (norm_le_one w) with hw | hw
  · have h8 : toZModPow 3 (w * w - 5) = 4 := by
      rw [map_sub, toZModPow_three_mul_self hw, toZModPow_three_five]
      decide
    obtain ⟨m, hm, hz⟩ := eq_four_mul_unit h8
    exact ⟨2, m, two_ne_zero_padicIntTwo, hm, by rw [hz]; ring⟩
  · refine ⟨1, w * w - 5, one_ne_zero, ?_, by ring⟩
    refine norm_eq_one_of_toZMod_ne_zero ?_
    rw [map_sub, map_mul, toZMod_eq_zero_of_norm_lt_one hw, toZMod_five]
    decide

/-- The companion form `1 - 5 w ²` is likewise a square times a unit. -/
theorem exists_unit_one_sub_five_mul_self (w : ℤ_[2]) :
    ∃ t m : ℤ_[2], t ≠ 0 ∧ ‖m‖ = 1 ∧ 1 - 5 * (w * w) = t * t * m := by
  rcases eq_or_lt_of_le (norm_le_one w) with hw | hw
  · have h8 : toZModPow 3 (1 - 5 * (w * w)) = 4 := by
      rw [map_sub, map_one, map_mul, toZModPow_three_mul_self hw, toZModPow_three_five]
      decide
    obtain ⟨m, hm, hz⟩ := eq_four_mul_unit h8
    exact ⟨2, m, two_ne_zero_padicIntTwo, hm, by rw [hz]; ring⟩
  · refine ⟨1, 1 - 5 * (w * w), one_ne_zero, ?_, by ring⟩
    refine norm_eq_one_of_toZMod_ne_zero ?_
    rw [map_sub, map_one, map_mul, map_mul, toZMod_eq_zero_of_norm_lt_one hw, toZMod_five]
    decide

/-- A nonzero dyadic integer stays nonzero in the dyadic field. -/
theorem coe_ne_zero_of_ne_zero {t : ℤ_[2]} (ht : t ≠ 0) : ((t : ℤ_[2]) : ℚ_[2]) ≠ 0 :=
  fun h => ht (Subtype.ext h)

/-- Two is nonzero in the dyadic field. -/
theorem two_ne_zero_padicTwo : (2 : ℚ_[2]) ≠ 0 := by
  have h : ((2 : ℕ) : ℚ_[2]) = 2 := by norm_cast
  rw [← h]
  exact_mod_cast (Fact.out : Nat.Prime 2).ne_zero

/-- The valuation of two in the dyadic field is one. -/
theorem valuation_two : (2 : ℚ_[2]).valuation = 1 := by
  have h : ((2 : ℕ) : ℚ_[2]) = 2 := by norm_cast
  rw [← h, Padic.valuation_p]

/-- **The norm form of `ℚ_2(√5)` takes only values of even valuation.** Every value at
arguments not both zero is a square times a unit. -/
theorem exists_sq_mul_unit_eq_normFormFive {a b : ℚ_[2]} (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ s m : ℚ_[2], s ≠ 0 ∧ ‖m‖ = 1 ∧ a * a - 5 * (b * b) = s * s * m := by
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
    obtain ⟨t, m, ht, hm, hEq⟩ := exists_unit_mul_self_sub_five ⟨a / b, hw⟩
    have hcast : (a / b) * (a / b) - 5 =
        ((t : ℤ_[2]) : ℚ_[2]) * ((t : ℤ_[2]) : ℚ_[2]) * ((m : ℤ_[2]) : ℚ_[2]) := by
      have hc := congrArg (fun z : ℤ_[2] => ((z : ℚ_[2]))) hEq
      push_cast at hc
      exact hc
    refine ⟨b * ((t : ℤ_[2]) : ℚ_[2]), ((m : ℤ_[2]) : ℚ_[2]),
      mul_ne_zero hb (coe_ne_zero_of_ne_zero ht), ?_, ?_⟩
    · rw [← PadicInt.norm_def]
      exact hm
    · field_simp at hcast
      linear_combination hcast
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
    obtain ⟨t, m, ht, hm, hEq⟩ := exists_unit_one_sub_five_mul_self ⟨b / a, hw⟩
    have hcast : 1 - 5 * ((b / a) * (b / a)) =
        ((t : ℤ_[2]) : ℚ_[2]) * ((t : ℤ_[2]) : ℚ_[2]) * ((m : ℤ_[2]) : ℚ_[2]) := by
      have hc := congrArg (fun z : ℤ_[2] => ((z : ℚ_[2]))) hEq
      push_cast at hc
      exact hc
    refine ⟨a * ((t : ℤ_[2]) : ℚ_[2]), ((m : ℤ_[2]) : ℚ_[2]),
      mul_ne_zero ha (coe_ne_zero_of_ne_zero ht), ?_, ?_⟩
    · rw [← PadicInt.norm_def]
      exact hm
    · field_simp at hcast
      linear_combination hcast

/-- **Two is not a norm from `ℚ_2(√5)`.** The norm form takes only values of even
valuation, and two has valuation one. -/
theorem not_isNormFromSqrt_five_two : ¬ IsNormFromSqrt (5 : ℚ_[2]) (2 : ℚ_[2]) := by
  rintro ⟨a, b, hab⟩
  have hne : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [hcon.1, hcon.2] at hab
    exact two_ne_zero_padicTwo (by linear_combination hab)
  obtain ⟨s, m, hs, hm, heq⟩ := exists_sq_mul_unit_eq_normFormFive hne
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, norm_zero] at hm
    exact zero_ne_one hm
  have hval : (2 : ℚ_[2]).valuation = (s * s * m).valuation := by rw [← heq, ← hab]
  rw [Padic.valuation_mul (mul_ne_zero hs hs) hm0, Padic.valuation_mul hs hs,
    valuation_eq_zero_of_norm_eq_one hm0 hm, valuation_two] at hval
  omega

/-- The residue of two modulo eight. -/
theorem toZModPow_three_two : toZModPow 3 (2 : ℤ_[2]) = 2 := by
  have h : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_cast
  rw [← h, map_natCast]
  decide

/-- The residue of four modulo two. -/
theorem toZMod_four : toZMod (4 : ℤ_[2]) = 0 := by
  have h : ((4 : ℕ) : ℤ_[2]) = 4 := by norm_cast
  rw [← h, map_natCast]
  decide

/-- A dyadic integer congruent to two modulo eight is two times a unit. -/
theorem eq_two_mul_unit {z : ℤ_[2]} (h : toZModPow 3 z = 2) :
    ∃ m : ℤ_[2], ‖m‖ = 1 ∧ z = 2 * m := by
  have hmem : z - 2 ∈ RingHom.ker (toZModPow (p := 2) 3) := by
    rw [RingHom.mem_ker, map_sub, h, toZModPow_three_two, sub_self]
  rw [ker_toZModPow] at hmem
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hmem
  refine ⟨1 + 4 * t, ?_, ?_⟩
  · refine norm_eq_one_of_toZMod_ne_zero ?_
    rw [map_add, map_one, map_mul, toZMod_four, zero_mul, add_zero]
    exact one_ne_zero
  · have h8 : ((2 : ℕ) : ℤ_[2]) ^ 3 = 8 := by
      push_cast
      norm_num
    rw [h8] at ht
    linear_combination ht

/-- The value `w ² + 1` of the norm form of the Gaussian dyadic extension is a unit when
`w` is not a unit, and twice a unit when `w` is a unit. -/
theorem mul_self_add_one_cases (W : ℤ_[2]) :
    (‖W‖ < 1 ∧ ‖W * W + 1‖ = 1) ∨ ∃ m : ℤ_[2], ‖m‖ = 1 ∧ W * W + 1 = 2 * m := by
  rcases eq_or_lt_of_le (norm_le_one W) with hW | hW
  · refine Or.inr (eq_two_mul_unit ?_)
    rw [map_add, map_one, toZModPow_three_mul_self hW]
    decide
  · refine Or.inl ⟨hW, norm_eq_one_of_toZMod_ne_zero ?_⟩
    rw [map_add, map_one, map_mul, toZMod_eq_zero_of_norm_lt_one hW]
    decide

/-- **The Gaussian dyadic extension does not have `-1` as a norm.** If the norm form is a
unit the residues modulo eight are incompatible; if it is twice a unit the valuation is
odd. -/
theorem not_neg_one_eq_sq_mul (c : ℚ_[2]) (hc : c ≠ 0) (W : ℤ_[2]) :
    (-1 : ℚ_[2]) ≠ c * c * ((W * W + 1 : ℤ_[2]) : ℚ_[2]) := by
  intro heq
  have hv1 : (-1 : ℚ_[2]).valuation = 0 :=
    valuation_eq_zero_of_norm_eq_one (neg_ne_zero.mpr one_ne_zero) (by simp)
  rcases mul_self_add_one_cases W with ⟨hW, hunit⟩ | ⟨m, hm, hz⟩
  · have hu0 : ((W * W + 1 : ℤ_[2]) : ℚ_[2]) ≠ 0 := by
      refine coe_ne_zero_of_ne_zero ?_
      intro h0
      rw [h0, norm_zero] at hunit
      exact zero_ne_one hunit
    have hunorm : ‖((W * W + 1 : ℤ_[2]) : ℚ_[2])‖ = 1 := by
      rw [← PadicInt.norm_def]
      exact hunit
    have hval := congrArg Padic.valuation heq
    rw [hv1, Padic.valuation_mul (mul_ne_zero hc hc) hu0, Padic.valuation_mul hc hc,
      valuation_eq_zero_of_norm_eq_one hu0 hunorm] at hval
    have hvc : c.valuation = 0 := by omega
    have hcnorm : ‖c‖ = 1 := by
      rw [Padic.norm_eq_zpow_neg_valuation hc, hvc]
      norm_num
    obtain ⟨C, hCval⟩ : ∃ C : ℤ_[2], (C : ℚ_[2]) = c := ⟨⟨c, le_of_eq hcnorm⟩, rfl⟩
    have hCnorm : ‖C‖ = 1 := by
      rw [PadicInt.norm_def, hCval]
      exact hcnorm
    have hZ : (-1 : ℤ_[2]) = C * C * (W * W + 1) := by
      refine Subtype.ext ?_
      push_cast [hCval]
      exact heq
    obtain ⟨t, ht⟩ := (PadicInt.norm_lt_one_iff_dvd W).mp hW
    have hW2 : toZModPow 3 W = 2 * toZModPow 3 t := by
      rw [ht, map_mul, map_natCast]
      norm_num
    have hres := congrArg (toZModPow (p := 2) 3) hZ
    rw [map_neg, map_one, map_mul, toZModPow_three_mul_self hCnorm, map_add, map_one,
      map_mul, hW2] at hres
    revert hres
    have hdec : ∀ z : ZMod 8, ¬ ((-1 : ZMod 8) = 1 * (2 * z * (2 * z) + 1)) := by decide
    exact hdec _
  · have hm0 : ((m : ℤ_[2]) : ℚ_[2]) ≠ 0 := by
      refine coe_ne_zero_of_ne_zero ?_
      intro h0
      rw [h0, norm_zero] at hm
      exact zero_ne_one hm
    have hmnorm : ‖((m : ℤ_[2]) : ℚ_[2])‖ = 1 := by
      rw [← PadicInt.norm_def]
      exact hm
    have hcast : ((W * W + 1 : ℤ_[2]) : ℚ_[2]) = 2 * ((m : ℤ_[2]) : ℚ_[2]) := by
      rw [hz]
      norm_cast
    rw [hcast] at heq
    have hval := congrArg Padic.valuation heq
    rw [hv1, Padic.valuation_mul (mul_ne_zero hc hc)
        (mul_ne_zero two_ne_zero_padicTwo hm0), Padic.valuation_mul hc hc,
      Padic.valuation_mul two_ne_zero_padicTwo hm0, valuation_two,
      valuation_eq_zero_of_norm_eq_one hm0 hmnorm] at hval
    omega

/-- **Minus one is not a sum of two dyadic squares.** -/
theorem not_isNormFromSqrt_negOne_negOne : ¬ IsNormFromSqrt (-1 : ℚ_[2]) (-1 : ℚ_[2]) := by
  rintro ⟨x, y, hxy⟩
  rcases le_total ‖x‖ ‖y‖ with h | h
  · have hy : y ≠ 0 := by
      intro hy0
      rw [hy0, norm_zero] at h
      have hx0 : x = 0 := norm_eq_zero.mp (le_antisymm h (norm_nonneg x))
      rw [hx0, hy0] at hxy
      exact (neg_ne_zero.mpr one_ne_zero) (by linear_combination hxy)
    have hypos : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
    have hw : ‖x / y‖ ≤ 1 := by
      rw [norm_div]
      exact (div_le_one hypos).mpr h
    refine not_neg_one_eq_sq_mul y hy ⟨x / y, hw⟩ ?_
    push_cast
    field_simp
    linear_combination hxy
  · have hx : x ≠ 0 := by
      intro hx0
      rw [hx0, norm_zero] at h
      have hy0 : y = 0 := norm_eq_zero.mp (le_antisymm h (norm_nonneg y))
      rw [hx0, hy0] at hxy
      exact (neg_ne_zero.mpr one_ne_zero) (by linear_combination hxy)
    have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    have hw : ‖y / x‖ ≤ 1 := by
      rw [norm_div]
      exact (div_le_one hxpos).mpr h
    refine not_neg_one_eq_sq_mul x hx ⟨y / x, hw⟩ ?_
    push_cast
    field_simp
    linear_combination hxy

/-! ## The closed formula -/

/-- **The symbol of `-1` against itself is `-1`.** -/
theorem hilbertSymbol_negOne_negOne_eq_neg_one :
    hilbertSymbol ((negOne : ℚ_[2]ˣ) : ℚ_[2]) ((negOne : ℚ_[2]ˣ) : ℚ_[2]) = -1 := by
  rw [coe_negOne]
  rcases hilbertSymbol_eq_one_or_neg_one (a := (-1 : ℚ_[2])) (b := (-1 : ℚ_[2]))
    (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero) with h | h
  · exact absurd ((hilbertSymbol_eq_one_iff_isNormFromSqrt (neg_ne_zero.mpr one_ne_zero)
      (neg_ne_zero.mpr one_ne_zero)).mp h) not_isNormFromSqrt_negOne_negOne
  · exact h

/-- **The symbol of `5` against `2` is `-1`.** -/
theorem hilbertSymbol_five_two_eq_neg_one :
    hilbertSymbol ((five : ℚ_[2]ˣ) : ℚ_[2]) ((pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]) = -1 := by
  have hf5 : (5 : ℚ_[2]) ≠ 0 := coe_five ▸ Units.ne_zero five
  have h2 : ((pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]) = 2 := by
    rw [coe_pUnit]
    norm_cast
  rw [coe_five, h2]
  rcases hilbertSymbol_eq_one_or_neg_one hf5 two_ne_zero_padicTwo with h | h
  · exact absurd ((hilbertSymbol_eq_one_iff_isNormFromSqrt hf5 two_ne_zero_padicTwo).mp h)
      not_isNormFromSqrt_five_two
  · exact h

/-- The exponent is additive in its first entry. -/
theorem dyadicPairing_mul_left (x y z : ℚ_[2]ˣ) :
    dyadicPairing (dyadicCoord (x * y)) (dyadicCoord z) =
      dyadicPairing (dyadicCoord x) (dyadicCoord z) +
        dyadicPairing (dyadicCoord y) (dyadicCoord z) := by
  rw [dyadicPairing, dyadicPairing, dyadicPairing, dyadicCoord_mul,
    dyadicEps_mul (isUnit_dyadicCoord_snd x) (isUnit_dyadicCoord_snd y),
    dyadicOmega_mul (isUnit_dyadicCoord_snd x) (isUnit_dyadicCoord_snd y)]
  ring

/-- The closed formula, as a property of the first entry. -/
def DyadicFormulaAt (x : ℚ_[2]ˣ) : Prop :=
  ∀ y : ℚ_[2]ˣ, hilbertSymbol (x : ℚ_[2]) (y : ℚ_[2]) =
    (((-1 : ℤˣ) ^ dyadicPairing (dyadicCoord x) (dyadicCoord y) : ℤˣ) : ℤ)

/-- A witness of exponent one with symbol `-1` forces the formula, because the symbol is
multiplicative in its second entry. -/
theorem dyadicFormulaAt_of_witness {g w : ℚ_[2]ˣ}
    (hgw : hilbertSymbol (g : ℚ_[2]) (w : ℚ_[2]) = -1)
    (hp : dyadicPairing (dyadicCoord g) (dyadicCoord w) = 1) : DyadicFormulaAt g := by
  intro y
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1)
      (dyadicPairing (dyadicCoord g) (dyadicCoord y)) with h | h
  · rw [h, uzpow_zero, Units.val_one]
    exact hilbertSymbol_eq_one_of_dyadicPairing_eq_zero g y h
  · have hzero : dyadicPairing (dyadicCoord g) (dyadicCoord (y * w)) = 0 := by
      rw [dyadicPairing_mul, h, hp]
      decide
    have h1 : hilbertSymbol (g : ℚ_[2]) ((y * w : ℚ_[2]ˣ) : ℚ_[2]) = 1 :=
      hilbertSymbol_eq_one_of_dyadicPairing_eq_zero g (y * w) hzero
    rw [Units.val_mul, hilbertSymbol_mul_right, hgw] at h1
    rw [h, uzpow_one, Units.val_neg, Units.val_one]
    linarith

/-- The formula holds for the class of one. -/
theorem dyadicFormulaAt_one : DyadicFormulaAt (1 : ℚ_[2]ˣ) := by
  intro y
  have h : dyadicPairing (dyadicCoord (1 : ℚ_[2]ˣ)) (dyadicCoord y) = 0 := by
    rw [dyadicCoord_one]
    revert y
    have hdec : ∀ d : ZMod 2 × ZMod 8, dyadicPairing (0, 1) d = 0 := by decide
    exact fun y => hdec (dyadicCoord y)
  rw [h, uzpow_zero, Units.val_one, Units.val_one]
  exact hilbertSymbol_one_left _ (Units.ne_zero y)

/-- The formula holds for the class of `-1`. -/
theorem dyadicFormulaAt_negOne : DyadicFormulaAt negOne :=
  dyadicFormulaAt_of_witness hilbertSymbol_negOne_negOne_eq_neg_one
    (by rw [dyadicCoord_negOne]; decide)

/-- The formula holds for the class of `5`. -/
theorem dyadicFormulaAt_five : DyadicFormulaAt five :=
  dyadicFormulaAt_of_witness hilbertSymbol_five_two_eq_neg_one
    (by rw [dyadicCoord_five, dyadicCoord_two]; decide)

/-- The formula holds for the class of `2`. -/
theorem dyadicFormulaAt_two : DyadicFormulaAt (pUnit 2) := by
  have hw : hilbertSymbol ((pUnit 2 : ℚ_[2]ˣ) : ℚ_[2]) ((five : ℚ_[2]ˣ) : ℚ_[2]) = -1 := by
    rw [hilbertSymbol_comm]
    exact hilbertSymbol_five_two_eq_neg_one
  have hp : dyadicPairing (dyadicCoord (pUnit 2)) (dyadicCoord five) = 1 := by
    rw [dyadicCoord_five, dyadicCoord_two]
    decide
  exact dyadicFormulaAt_of_witness hw hp

/-- The formula is closed under products, by bilinearity. -/
theorem DyadicFormulaAt.mul {x₁ x₂ : ℚ_[2]ˣ} (h₁ : DyadicFormulaAt x₁)
    (h₂ : DyadicFormulaAt x₂) : DyadicFormulaAt (x₁ * x₂) := by
  intro y
  rw [Units.val_mul, HasBilinearHilbertSymbol.map_mul_left, h₁ y, h₂ y,
    dyadicPairing_mul_left, uzpow_add, Units.val_mul]

/-- The formula depends only on the square class of the first entry. -/
theorem DyadicFormulaAt.of_coord_eq {x r : ℚ_[2]ˣ} (h : dyadicCoord x = dyadicCoord r)
    (hr : DyadicFormulaAt r) : DyadicFormulaAt x := by
  intro y
  rw [hilbertSymbol_congr_left h y, h]
  exact hr y

/-- **The closed formula for the dyadic Hilbert symbol.** Writing `a = 2 ^ α u` and
`b = 2 ^ β v` with dyadic units `u` and `v`, the symbol is
`(-1) ^ (ε(u) ε(v) + α ω(v) + β ω(u))`, where `ε` and `ω` are the parities of `(u-1)/2` and
`(u ² - 1)/8`, both functions of the residue of the unit modulo eight.

This is Serre, *A Course in Arithmetic*, Ch. III §1.2, Theorem 1 [@Ser73, p. 20]. -/
theorem hilbertSymbol_dyadic_formula (x y : ℚ_[2]ˣ) :
    hilbertSymbol (x : ℚ_[2]) (y : ℚ_[2]) =
      (((-1 : ℤˣ) ^ dyadicPairing (dyadicCoord x) (dyadicCoord y) : ℤˣ) : ℤ) := by
  have hcases : ∀ c : ZMod 2 × ZMod 8, (∃ e, c.2 * e = 1) →
      c = (0, 1) ∨ c = (0, 7) ∨ c = (0, 5) ∨ c = (0, 3) ∨
        c = (1, 1) ∨ c = (1, 7) ∨ c = (1, 5) ∨ c = (1, 3) := by decide
  rcases hcases (dyadicCoord x) (exists_inv_dyadicCoord_snd x) with
    hx | hx | hx | hx | hx | hx | hx | hx
  · exact DyadicFormulaAt.of_coord_eq (by rw [hx, dyadicCoord_one]) dyadicFormulaAt_one y
  · exact DyadicFormulaAt.of_coord_eq (by rw [hx, dyadicCoord_negOne]) dyadicFormulaAt_negOne y
  · exact DyadicFormulaAt.of_coord_eq (by rw [hx, dyadicCoord_five]) dyadicFormulaAt_five y
  · exact DyadicFormulaAt.of_coord_eq (by rw [hx, dyadicCoord_negFive])
      (dyadicFormulaAt_negOne.mul dyadicFormulaAt_five) y
  · exact DyadicFormulaAt.of_coord_eq (by rw [hx, dyadicCoord_two]) dyadicFormulaAt_two y
  · exact DyadicFormulaAt.of_coord_eq (by rw [hx, dyadicCoord_negTwo])
      (dyadicFormulaAt_negOne.mul dyadicFormulaAt_two) y
  · exact DyadicFormulaAt.of_coord_eq (by rw [hx, dyadicCoord_ten])
      (dyadicFormulaAt_five.mul dyadicFormulaAt_two) y
  · exact DyadicFormulaAt.of_coord_eq (by rw [hx, dyadicCoord_negTen])
      ((dyadicFormulaAt_negOne.mul dyadicFormulaAt_five).mul dyadicFormulaAt_two) y

end Padic

end LeanCategories.Lattices.Valued

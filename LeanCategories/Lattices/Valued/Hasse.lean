/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.LocalInvariants
public import LeanCategories.Lattices.Valued.Signature
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

@[expose] public section

namespace LeanCategories.Lattices.Valued

universe u

variable {K : Type u} [Field K]

/--
The Hilbert symbol, defined by isotropy of `z² - a x² - b y²`.

This is the local-field definition in Milne [@Mil20b, p. 210]. The Lean construction
follows `HassePrinciple/HilbertSymbol/Basic.lean` in `mariainesdff/HassePrinciple`.
-/
noncomputable def hilbertSymbol (a b : K) : ℤ := by
  classical
  exact if a = 0 ∨ b = 0 then 0
    else if ∃ z x y : K,
      (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0
    then 1 else -1

/-- The Hilbert symbol is symmetric.

This is Milne's Proposition 4.6(a) [@Mil20b, p. 211]. -/
theorem hilbertSymbol_comm (a b : K) :
    hilbertSymbol a b = hilbertSymbol b a := by
  classical
  by_cases ha : a = 0
  · subst a
    simp [hilbertSymbol]
  by_cases hb : b = 0
  · subst b
    simp [hilbertSymbol]
  simp only [hilbertSymbol, ha, hb, or_false, ↓reduceIte]
  congr 1
  apply propext
  constructor
  · rintro ⟨z, x, y, hne, hzero⟩
    refine ⟨z, y, x, ?_, ?_⟩
    · aesop
    · linear_combination hzero
  · rintro ⟨z, x, y, hne, hzero⟩
    refine ⟨z, y, x, ?_, ?_⟩
    · aesop
    · linear_combination hzero

/-- The Hilbert symbol of two nonzero elements is `1` or `-1`. -/
theorem hilbertSymbol_eq_one_or_neg_one {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol a b = 1 ∨ hilbertSymbol a b = -1 := by
  classical
  simp only [hilbertSymbol, ha, hb, false_or, ↓reduceIte]
  split_ifs <;> simp

/-- Multiplying both entries by nonzero squares does not change the Hilbert symbol.

This is Milne's Proposition 4.6(b) [@Mil20b, p. 211]. The proof follows
`HassePrinciple.HilbertSymbol.Basic.hilbertSym.mul_square_eq`.
-/
theorem hilbertSymbol_mul_square (a b : K) {s t : K} (hs : s ≠ 0) (ht : t ≠ 0) :
    hilbertSymbol (a * s ^ 2) (b * t ^ 2) = hilbertSymbol a b := by
  classical
  simp only [hilbertSymbol, mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    pow_eq_zero_iff, Prod.mk.injEq, not_and, Int.reduceNeg]
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  simp only [ha, hb, hs, ht, or_false, ↓reduceIte]
  split_ifs with h h' h'
  · rfl
  · obtain ⟨z, x, y, h0, heq⟩ := h
    exact h' ⟨z, s * x, t * y, by aesop, by rw [← heq]; ring⟩
  · obtain ⟨z, x, y, h0, heq⟩ := h'
    apply h
    refine ⟨z, (1 / s) * x, (1 / t) * y, by aesop, ?_⟩
    field_simp
    rw [heq]
  · rfl

/-- Multiplying the first entry by a nonzero square does not change the Hilbert symbol. -/
@[simp]
theorem hilbertSymbol_mul_square_left (a b : K) {s : K} (hs : s ≠ 0) :
    hilbertSymbol (a * s ^ 2) b = hilbertSymbol a b := by
  nth_rw 1 [← mul_one b]
  rw [← one_pow 2, hilbertSymbol_mul_square a b hs one_ne_zero]

/-- Multiplying the second entry by a nonzero square does not change the Hilbert symbol. -/
@[simp]
theorem hilbertSymbol_mul_square_right (a b : K) {t : K} (ht : t ≠ 0) :
    hilbertSymbol a (b * t ^ 2) = hilbertSymbol a b := by
  nth_rw 1 [← mul_one a]
  rw [← one_pow 2, hilbertSymbol_mul_square a b one_ne_zero ht]

/-- The Hilbert symbol of `a` and `-a` is one when `a` is nonzero. -/
@[simp]
theorem hilbertSymbol_neg_self (a : K) (ha : a ≠ 0) :
    hilbertSymbol a (-a) = 1 := by
  classical
  rw [hilbertSymbol, if_neg (by simp [ha]), if_pos]
  exact ⟨0, 1, 1, by simp, by ring⟩

/-- The Hilbert symbol of `a` and `1-a` is one away from zero and one. -/
@[simp]
theorem hilbertSymbol_one_sub_self (a : K) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    hilbertSymbol a (1 - a) = 1 := by
  classical
  rw [hilbertSymbol, if_neg (by simp [ha0, sub_ne_zero.mpr ha1.symm]), if_pos]
  exact ⟨1, 1, 1, by simp, by ring⟩

/-- A field has a bilinear Hilbert symbol when the symbol is multiplicative in one entry.

By symmetry, this is equivalent to multiplicativity in both entries. Milne proves this for
local fields in Proposition 4.6(c) [@Mil20b, p. 211]. -/
class HasBilinearHilbertSymbol (K : Type u) [Field K] : Prop where
  map_mul_left {a b c : K} :
    hilbertSymbol (a * b) c = hilbertSymbol a c * hilbertSymbol b c

/-- Bilinearity in the second entry follows from symmetry. -/
theorem hilbertSymbol_mul_right [HasBilinearHilbertSymbol K] (a b c : K) :
    hilbertSymbol a (b * c) = hilbertSymbol a b * hilbertSymbol a c := by
  rw [hilbertSymbol_comm, HasBilinearHilbertSymbol.map_mul_left,
    hilbertSymbol_comm b, hilbertSymbol_comm c]

/-- The standard relation `(a, -ab) = (a, b)` for a bilinear Hilbert symbol. -/
@[simp]
theorem hilbertSymbol_neg_mul [HasBilinearHilbertSymbol K] (a b : K) :
    hilbertSymbol a (-(a * b)) = hilbertSymbol a b := by
  by_cases ha : a = 0
  · simp [ha, hilbertSymbol]
  rw [← neg_mul, hilbertSymbol_mul_right, hilbertSymbol_neg_self a ha]
  simp

/-- Over `ℝ`, the Hilbert symbol is `-1` precisely when both entries are negative. -/
theorem hilbertSymbol_real {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol a b = if 0 < a ∨ 0 < b then 1 else -1 := by
  split_ifs with h
  · wlog ha_pos : 0 < a generalizing a b with swap
    · rw [hilbertSymbol_comm]
      exact swap hb ha (by tauto) (by tauto)
    simp only [hilbertSymbol, ha, hb, or_self, ↓reduceIte, ne_eq, Prod.mk.injEq,
      not_and, Int.reduceNeg, ite_eq_left_iff, not_exists, reduceCtorEq, imp_false,
      not_forall, Decidable.not_not]
    exact ⟨Real.sqrt a, 1, 0, by simp, by simp [Real.sq_sqrt ha_pos.le]⟩
  · simp only [not_or, not_lt] at h
    simp only [hilbertSymbol, ha, hb, or_self, ↓reduceIte, ne_eq, Prod.mk.injEq,
      not_and, sub_sub, Int.reduceNeg, ite_eq_right_iff, reduceCtorEq, imp_false,
      not_exists, sub_eq_add_neg _ (_ + _)]
    intro z x y h0
    have hz : 0 ≤ z ^ 2 := by positivity
    have hax : 0 ≤ -a * x ^ 2 := by positivity [Left.nonneg_neg_iff.mpr h.1]
    have hby : 0 ≤ -b * y ^ 2 := by positivity [Left.nonneg_neg_iff.mpr h.2]
    have zero_terms {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 0) :
        r = 0 ∧ s = 0 :=
      (add_eq_zero_iff_of_nonneg hr hs).mp hrs
    grind

/-- The Hilbert symbol is bilinear over the real local field. -/
instance : HasBilinearHilbertSymbol ℝ where
  map_mul_left {a b c} := by
    by_cases h0 : a = 0 ∨ b = 0 ∨ c = 0
    · rcases h0 with h0 | h0 | h0 <;> simp [hilbertSymbol, h0]
    simp only [not_or] at h0
    obtain ⟨ha, hb, hc⟩ := h0
    rw [hilbertSymbol_real ha hc, hilbertSymbol_real hb hc,
      hilbertSymbol_real (mul_ne_zero ha hb) hc]
    rcases lt_or_gt_of_ne (Ne.symm ha) with ha_pos | ha_neg
    · simp [ha_pos]
    · by_cases hc_pos : 0 < c
      · simp [hc_pos]
      · by_cases hb_pos : 0 < b
        · simp [not_lt_of_ge ha_neg.le, hb_pos, hc_pos]
        · have hb_neg : b < 0 := lt_of_le_of_ne (not_lt.mp hb_pos) hb
          simp [not_lt_of_ge ha_neg.le, hb_pos, hc_pos,
            mul_pos_of_neg_of_neg ha_neg hb_neg]

/-- The Hasse--Minkowski value of a diagonal list of nonzero coefficients.

Cassels defines this value as `∏ i < j, (a_i, a_j)` [@Cas08a, p. 55]. -/
noncomputable def hasseMinkowskiInvariantOfDiagonal
    {n : ℕ} (w : Fin n → Kˣ) : ℤ :=
  ∏ p : Fin n × Fin n with p.1 < p.2,
    hilbertSymbol (w p.1 : K) (w p.2 : K)

/-- A unary diagonal form has Hasse--Minkowski value one.

This is the first case of Cassels's Lemma 2.2 [@Cas08a, p. 56]. -/
@[simp]
theorem hasseMinkowskiInvariantOfDiagonal_one (w : Fin 1 → Kˣ) :
    hasseMinkowskiInvariantOfDiagonal w = 1 := by
  rw [hasseMinkowskiInvariantOfDiagonal]
  exact Finset.prod_eq_one fun p hp => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have : p.1 = p.2 := Subsingleton.elim _ _
    exact (lt_irrefl p.2 (this ▸ hp)).elim

/-- A binary diagonal form has Hasse--Minkowski value equal to one Hilbert symbol.

This is the binary case used in Cassels's Lemma 2.2 [@Cas08a, p. 56]. -/
theorem hasseMinkowskiInvariantOfDiagonal_two (w : Fin 2 → Kˣ) :
    hasseMinkowskiInvariantOfDiagonal w =
      hilbertSymbol (w 0 : K) (w 1 : K) := by
  rw [hasseMinkowskiInvariantOfDiagonal,
    Finset.prod_eq_single (0, 1) (by grind) (fun h => by simp at h)]

/-- Swapping the two coefficients of a binary diagonal form preserves its value. -/
theorem hasseMinkowskiInvariantOfDiagonal_two_swap (w : Fin 2 → Kˣ) :
    hasseMinkowskiInvariantOfDiagonal (fun i => w (Equiv.swap 0 1 i)) =
      hasseMinkowskiInvariantOfDiagonal w := by
  rw [hasseMinkowskiInvariantOfDiagonal_two, hasseMinkowskiInvariantOfDiagonal_two]
  simpa using hilbertSymbol_comm (w 1 : K) (w 0 : K)

/-- Rescaling diagonal coordinates does not change their Hasse--Minkowski value. -/
theorem hasseMinkowskiInvariantOfDiagonal_squareRescale
    {n : ℕ} (w w' u : Fin n → Kˣ)
    (h : ∀ i, w' i * u i ^ 2 = w i) :
    hasseMinkowskiInvariantOfDiagonal w =
      hasseMinkowskiInvariantOfDiagonal w' := by
  classical
  unfold hasseMinkowskiInvariantOfDiagonal
  apply Finset.prod_congr rfl
  intro p hp
  rw [← h p.1, ← h p.2]
  exact hilbertSymbol_mul_square
    (w' p.1 : K) (w' p.2 : K) (Units.ne_zero (u p.1)) (Units.ne_zero (u p.2))

variable [Invertible (2 : K)]

/-- A diagonal presentation of a nondegenerate finite symmetric form. -/
structure DiagonalPresentation (L : FiniteFormCat K K)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated) where
  weights : Fin (Module.finrank K L.obj.carrier) → Kˣ
  equivalent : QuadraticMap.Equivalent
    (finiteFormQuadraticForm K L)
    (QuadraticMap.weightedSumSquares K weights)

/-- Rescale the coordinates of a diagonal presentation by units. -/
noncomputable def DiagonalPresentation.rescale
    {L : FiniteFormCat K K}
    {hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated}
    (d : DiagonalPresentation L hL)
    (w' u : Fin (Module.finrank K L.obj.carrier) → Kˣ)
    (h : ∀ i, w' i * u i ^ 2 = d.weights i) :
    DiagonalPresentation L hL where
  weights := w'
  equivalent := d.equivalent.trans
    ⟨QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares
      (R := K) (S := K) u (fun i => by exact_mod_cast h i)⟩

/-- Every nondegenerate finite symmetric form has a diagonal presentation. -/
noncomputable def diagonalPresentation (L : FiniteFormCat K K)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated) : DiagonalPresentation L hL := by
  letI : Module.Finite K L.obj.carrier := L.property.1
  let h := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'
    (finiteFormQuadraticForm K L) hL
  exact ⟨h.choose, h.choose_spec⟩

/-- The Hasse--Minkowski value computed from one diagonal presentation. -/
noncomputable def DiagonalPresentation.hasseMinkowskiValue
    {L : FiniteFormCat K K}
    {hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated}
    (d : DiagonalPresentation L hL) : ℤ :=
  hasseMinkowskiInvariantOfDiagonal d.weights

/-- Coordinate rescaling preserves the value of a diagonal presentation. -/
theorem DiagonalPresentation.hasseMinkowskiValue_rescale
    {L : FiniteFormCat K K}
    {hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated}
    (d : DiagonalPresentation L hL)
    (w' u : Fin (Module.finrank K L.obj.carrier) → Kˣ)
    (h : ∀ i, w' i * u i ^ 2 = d.weights i) :
    (d.rescale w' u h).hasseMinkowskiValue = d.hasseMinkowskiValue := by
  exact (hasseMinkowskiInvariantOfDiagonal_squareRescale d.weights w' u h).symm

/-- A value is the Hasse--Minkowski invariant when every diagonal presentation computes it.

Cassels proves this independence before using the value as an invariant
[@Cas08a, Chapter 4, §2]. -/
def IsHasseMinkowskiInvariant (L : FiniteFormCat K K)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated) (c : ℤ) : Prop :=
  ∀ d : DiagonalPresentation L hL, d.hasseMinkowskiValue = c

/-- The determinant square class computed from a diagonal presentation. -/
noncomputable def DiagonalPresentation.determinantSquareClass
    {L : FiniteFormCat K K}
    {hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated}
    (d : DiagonalPresentation L hL) : FieldSquareClass K :=
  fieldSquareClass (∏ i, d.weights i)

/-- The rank, determinant square class, and Hasse--Minkowski value of a diagonal presentation. -/
structure DiagonalFormProfile (K : Type u) [Field K] where
  rank : ℕ
  determinant : FieldSquareClass K
  hasse : ℤ

/-- The profile computed from a selected diagonal presentation. -/
noncomputable def DiagonalPresentation.profile
    {L : FiniteFormCat K K}
    {hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated}
    (d : DiagonalPresentation L hL) : DiagonalFormProfile K where
  rank := Module.finrank K L.obj.carrier
  determinant := d.determinantSquareClass
  hasse := d.hasseMinkowskiValue

end LeanCategories.Lattices.Valued

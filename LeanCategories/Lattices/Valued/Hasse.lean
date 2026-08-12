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

/-- The Hasse--Minkowski value of a diagonal list of nonzero coefficients.

Cassels defines this value as `∏ i < j, (a_i, a_j)` [@Cas08a, p. 55]. -/
noncomputable def hasseMinkowskiInvariantOfDiagonal
    {n : ℕ} (w : Fin n → Kˣ) : ℤ :=
  ∏ p : Fin n × Fin n with p.1 < p.2,
    hilbertSymbol (w p.1 : K) (w p.2 : K)

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

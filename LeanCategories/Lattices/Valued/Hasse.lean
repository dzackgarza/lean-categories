/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.LocalInvariants
public import LeanCategories.Lattices.Valued.Signature
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

@[expose] public section

namespace LeanCategories.Lattices.Valued

universe u

open Module QuadraticMap

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

/-- The Hilbert symbol in the second entry depends only on its square class. -/
theorem hilbertSymbol_eq_of_fieldSquareClass_eq_right
    (a b c : Kˣ) (h : fieldSquareClass b = fieldSquareClass c) :
    hilbertSymbol (a : K) (b : K) = hilbertSymbol (a : K) (c : K) := by
  rw [fieldSquareClass, fieldSquareClass, QuotientGroup.mk'_eq_mk'] at h
  obtain ⟨z, hz, hbc⟩ := h
  obtain ⟨q, rfl⟩ := Subgroup.mem_square.mp hz
  rw [← hbc]
  simpa [pow_two, mul_assoc] using
    (hilbertSymbol_mul_square_right (a : K) (b : K) (Units.ne_zero q)).symm

/-- The Hilbert symbol in the first entry depends only on its square class. -/
theorem hilbertSymbol_eq_of_fieldSquareClass_eq_left
    (a b c : Kˣ) (h : fieldSquareClass a = fieldSquareClass b) :
    hilbertSymbol (a : K) (c : K) = hilbertSymbol (b : K) (c : K) := by
  rw [hilbertSymbol_comm (a : K), hilbertSymbol_comm (b : K)]
  exact hilbertSymbol_eq_of_fieldSquareClass_eq_right c a b h

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

/-- A product over increasing pairs is the product over each second index and its predecessors. -/
theorem prod_increasing_pairs_eq_prod_Iio
    {n : ℕ} {M : Type*} [CommMonoid M] (f : Fin n → Fin n → M) :
    (∏ p : Fin n × Fin n with p.1 < p.2, f p.1 p.2) =
      ∏ j : Fin n, ∏ i ∈ Finset.Iio j, f i j := by
  classical
  rw [Finset.prod_sigma']
  apply Finset.prod_bij
      (fun p _ ↦ ⟨p.2, ⟨p.1, by simp⟩⟩)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp [hp]
  · intro p hp q hq heq
    have h2 : p.2 = q.2 := by
      simpa using (congrArg Sigma.fst heq)
    rcases p with ⟨i, j⟩
    rcases q with ⟨i', j'⟩
    simp only at h2
    subst j'
    have h1 : i = i' := by
      apply Fin.ext
      simpa using congrArg (fun s ↦ s.2.1) heq
    exact Prod.ext h1 rfl
  · rintro ⟨j, i⟩ hj
    refine ⟨(i, j), ?_, ?_⟩
    · simpa using hj
    · simp
  · intro p hp
    rfl

/-- The Hasse--Minkowski value as an iterated product over earlier coefficients. -/
theorem hasseMinkowskiInvariantOfDiagonal_eq_prod_Iio
    {n : ℕ} (w : Fin n → Kˣ) :
    hasseMinkowskiInvariantOfDiagonal w =
      ∏ j : Fin n, ∏ i ∈ Finset.Iio j,
        hilbertSymbol (w i : K) (w j : K) := by
  exact prod_increasing_pairs_eq_prod_Iio fun i j ↦
    hilbertSymbol (w i : K) (w j : K)

/-- The predecessor product at a successor index splits off the zero index. -/
theorem prod_Iio_fin_succ
    {n : ℕ} {M : Type*} [CommMonoid M] (j : Fin n) (f : Fin (n + 1) → M) :
    (∏ i ∈ Finset.Iio j.succ, f i) =
      f 0 * ∏ i ∈ Finset.Iio j, f i.succ := by
  rw [show (Finset.Iio j.succ : Finset (Fin (n + 1))) =
      insert (0 : Fin (n + 1)) (Finset.map (Fin.succEmb n) (Finset.Iio j)) by
    ext i
    refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp]
  rw [Finset.prod_insert]
  · rw [Finset.prod_map]
    simp
  · simp

/-- Appending one diagonal coefficient gives the recursive Hasse product formula.

This is the product form used in Cassels's contiguous-basis proof of Lemma 2.2
[@Cas08a, p. 56].
-/
theorem hasseMinkowskiInvariantOfDiagonal_cons
    {n : ℕ} (a : Kˣ) (w : Fin n → Kˣ) :
    hasseMinkowskiInvariantOfDiagonal (Fin.cons a w) =
      hasseMinkowskiInvariantOfDiagonal w *
        ∏ i, hilbertSymbol (a : K) (w i : K) := by
  classical
  rw [hasseMinkowskiInvariantOfDiagonal_eq_prod_Iio,
    hasseMinkowskiInvariantOfDiagonal_eq_prod_Iio,
    Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  simp_rw [prod_Iio_fin_succ]
  have hzero : (Finset.Iio (0 : Fin (n + 1))) = ∅ := by
    ext i
    simp
  rw [hzero, Finset.prod_empty, one_mul]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Finset.prod_mul_distrib, mul_comm]

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

/-- Equivalent nonsingular binary diagonal forms have equal Hilbert symbols.

This is Cassels's corollary to Lemma 2.1 [@Cas08a, p. 56]. The proof transports
the defining isotropic vector through the isometry.
-/
theorem hilbertSymbol_eq_of_equivalent_weightedSumSquares_two
    (w w' : Fin 2 → Kˣ)
    (h : QuadraticMap.Equivalent
      (QuadraticMap.weightedSumSquares K w)
      (QuadraticMap.weightedSumSquares K w')) :
    hilbertSymbol (w 0 : K) (w 1 : K) =
      hilbertSymbol (w' 0 : K) (w' 1 : K) := by
  classical
  simp only [hilbertSymbol, Units.ne_zero, or_false, ↓reduceIte]
  congr 1
  apply propext
  let e := Classical.choice h
  constructor
  · rintro ⟨z, x, y, hne, heq⟩
    let v : Fin 2 → K := ![x, y]
    let v' := e v
    refine ⟨z, v' 0, v' 1, ?_, ?_⟩
    · intro hzero
      have hz : z = 0 := congrArg Prod.fst hzero
      have hv'0 : v' 0 = 0 := congrArg (fun p ↦ p.2.1) hzero
      have hv'1 : v' 1 = 0 := congrArg (fun p ↦ p.2.2) hzero
      have hv' : v' = 0 := by
        funext i
        fin_cases i <;> simp [hv'0, hv'1]
      have hv : v = 0 := e.injective (by simpa [v'] using hv')
      apply hne
      ext <;> simp_all [v]
    · have hmap := e.map_app v
      change QuadraticMap.weightedSumSquares K w' v' =
        QuadraticMap.weightedSumSquares K w v at hmap
      simp [QuadraticMap.weightedSumSquares_apply, v] at hmap
      simp [Units.smul_def] at hmap
      simp only [← pow_two] at hmap
      calc
        z ^ 2 - (w' 0 : K) * v' 0 ^ 2 - (w' 1 : K) * v' 1 ^ 2 =
            z ^ 2 - ((w' 0 : K) * v' 0 ^ 2 + (w' 1 : K) * v' 1 ^ 2) := by ring
        _ = z ^ 2 - ((w 0 : K) * x ^ 2 + (w 1 : K) * y ^ 2) := by rw [hmap]
        _ = 0 := by linear_combination heq
  · rintro ⟨z, x, y, hne, heq⟩
    let v : Fin 2 → K := ![x, y]
    let v' := e.symm v
    refine ⟨z, v' 0, v' 1, ?_, ?_⟩
    · intro hzero
      have hz : z = 0 := congrArg Prod.fst hzero
      have hv'0 : v' 0 = 0 := congrArg (fun p ↦ p.2.1) hzero
      have hv'1 : v' 1 = 0 := congrArg (fun p ↦ p.2.2) hzero
      have hv' : v' = 0 := by
        funext i
        fin_cases i <;> simp [hv'0, hv'1]
      have hv : v = 0 := e.symm.injective (by simpa [v'] using hv')
      apply hne
      ext <;> simp_all [v]
    · have hmap := e.symm.map_app v
      change QuadraticMap.weightedSumSquares K w v' =
        QuadraticMap.weightedSumSquares K w' v at hmap
      simp [QuadraticMap.weightedSumSquares_apply, v] at hmap
      simp [Units.smul_def] at hmap
      simp only [← pow_two] at hmap
      calc
        z ^ 2 - (w 0 : K) * v' 0 ^ 2 - (w 1 : K) * v' 1 ^ 2 =
            z ^ 2 - ((w 0 : K) * v' 0 ^ 2 + (w 1 : K) * v' 1 ^ 2) := by ring
        _ = z ^ 2 - ((w' 0 : K) * x ^ 2 + (w' 1 : K) * y ^ 2) := by rw [hmap]
        _ = 0 := by linear_combination heq

/-- Equivalent nonsingular binary diagonal forms have equal Hasse--Minkowski values. -/
theorem hasseMinkowskiInvariantOfDiagonal_two_eq_of_equivalent
    (w w' : Fin 2 → Kˣ)
    (h : QuadraticMap.Equivalent
      (QuadraticMap.weightedSumSquares K w)
      (QuadraticMap.weightedSumSquares K w')) :
    hasseMinkowskiInvariantOfDiagonal w =
      hasseMinkowskiInvariantOfDiagonal w' := by
  rw [hasseMinkowskiInvariantOfDiagonal_two,
    hasseMinkowskiInvariantOfDiagonal_two]
  exact hilbertSymbol_eq_of_equivalent_weightedSumSquares_two w w' h

/-- Swapping the two coefficients of a binary diagonal form preserves its value. -/
theorem hasseMinkowskiInvariantOfDiagonal_two_swap (w : Fin 2 → Kˣ) :
    hasseMinkowskiInvariantOfDiagonal (fun i => w (Equiv.swap 0 1 i)) =
      hasseMinkowskiInvariantOfDiagonal w := by
  rw [hasseMinkowskiInvariantOfDiagonal_two, hasseMinkowskiInvariantOfDiagonal_two]
  simpa using hilbertSymbol_comm (w 1 : K) (w 0 : K)

/-- Pairs of negative coefficients in a real diagonal presentation. -/
noncomputable def negativeCoefficientPairs {n : ℕ} (w : Fin n → ℝˣ) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ (w p.1 : ℝ) < 0 ∧ (w p.2 : ℝ) < 0

/-- The number of negative coefficient pairs depends only on the number of negative coefficients. -/
theorem negativeCoefficientPairs_card_eq_of_ncard_eq
    {n m : ℕ} {w : Fin n → ℝˣ} {w' : Fin m → ℝˣ}
    (hcard : {i | (w i : ℝ) < 0}.ncard = {i | (w' i : ℝ) < 0}.ncard) :
    (negativeCoefficientPairs w).card = (negativeCoefficientPairs w').card := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i => (w i : ℝ) < 0
  let t : Finset (Fin m) := Finset.univ.filter fun i => (w' i : ℝ) < 0
  have hst : s.card = t.card := by simpa [s, t, Set.ncard_eq_toFinset_card'] using hcard
  let e : s ≃o t :=
    (s.orderIsoOfFin rfl).symm.trans (t.orderIsoOfFin hst.symm)
  let pairEquiv : ↥(negativeCoefficientPairs w) ≃ ↥(negativeCoefficientPairs w') := {
    toFun p := by
      have hp := (Finset.mem_filter.mp p.2).2
      let i : s := ⟨p.1.1, by simpa [s] using hp.2.1⟩
      let j : s := ⟨p.1.2, by simpa [s] using hp.2.2⟩
      exact ⟨(e i, e j), by
        simp only [negativeCoefficientPairs, Finset.mem_filter, Finset.mem_univ, true_and]
        have hi : (w' (e i) : ℝ) < 0 :=
          (Finset.mem_filter.mp (show (e i : Fin m) ∈ t from (e i).2)).2
        have hj : (w' (e j) : ℝ) < 0 :=
          (Finset.mem_filter.mp (show (e j : Fin m) ∈ t from (e j).2)).2
        exact ⟨e.lt_iff_lt.mpr hp.1, hi, hj⟩⟩
    invFun p := by
      have hp := (Finset.mem_filter.mp p.2).2
      let i : t := ⟨p.1.1, by simpa [t] using hp.2.1⟩
      let j : t := ⟨p.1.2, by simpa [t] using hp.2.2⟩
      exact ⟨(e.symm i, e.symm j), by
        simp only [negativeCoefficientPairs, Finset.mem_filter, Finset.mem_univ, true_and]
        have hi : (w (e.symm i) : ℝ) < 0 :=
          (Finset.mem_filter.mp (show (e.symm i : Fin n) ∈ s from (e.symm i).2)).2
        have hj : (w (e.symm j) : ℝ) < 0 :=
          (Finset.mem_filter.mp (show (e.symm j : Fin n) ∈ s from (e.symm j).2)).2
        exact ⟨e.symm.lt_iff_lt.mpr hp.1, hi, hj⟩⟩
    left_inv p := by
      apply Subtype.ext
      apply Prod.ext <;> exact congr_arg Subtype.val (e.symm_apply_apply _)
    right_inv p := by
      apply Subtype.ext
      apply Prod.ext <;> exact congr_arg Subtype.val (e.apply_symm_apply _)
  }
  simpa using Fintype.card_congr pairEquiv

/-- Cassels's real formula for the Hasse--Minkowski value.

Each pair contributes `-1` exactly when both coefficients are negative. This is the
formula preceding Cassels's Theorem 1.2 [@Cas08a, p. 55]. -/
theorem hasseMinkowskiInvariantOfDiagonal_real (w : Fin n → ℝˣ) :
    hasseMinkowskiInvariantOfDiagonal w =
      (-1 : ℤ) ^ (negativeCoefficientPairs w).card := by
  classical
  rw [hasseMinkowskiInvariantOfDiagonal]
  calc
    (∏ p : Fin n × Fin n with p.1 < p.2,
        hilbertSymbol (w p.1 : ℝ) (w p.2 : ℝ)) =
        ∏ p : Fin n × Fin n with p.1 < p.2,
          if (w p.1 : ℝ) < 0 ∧ (w p.2 : ℝ) < 0 then -1 else 1 := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [hilbertSymbol_real (Units.ne_zero _) (Units.ne_zero _)]
      by_cases hn : (w p.1 : ℝ) < 0 ∧ (w p.2 : ℝ) < 0
      · simp [hn, not_lt_of_ge hn.1.le, not_lt_of_ge hn.2.le]
      · have hp : 0 < (w p.1 : ℝ) ∨ 0 < (w p.2 : ℝ) := by
          rcases lt_or_gt_of_ne (Ne.symm (Units.ne_zero (w p.1))) with h1 | h1
          · exact Or.inl h1
          · rcases lt_or_gt_of_ne (Ne.symm (Units.ne_zero (w p.2))) with h2 | h2
            · exact Or.inr h2
            · exact (hn ⟨h1, h2⟩).elim
        simp [hn, hp]
    _ = ∏ _p ∈ negativeCoefficientPairs w, (-1 : ℤ) := by
      rw [Finset.prod_ite]
      simp only [Finset.prod_const_one, mul_one]
      apply Finset.prod_congr
      · ext p
        simp [negativeCoefficientPairs]
      · simp
    _ = (-1 : ℤ) ^ (negativeCoefficientPairs w).card := Finset.prod_const (-1)

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

/-- The canonical Hasse--Minkowski invariant of a real nondegenerate form.

Cassels identifies it with `(-1)^(s(s-1)/2)`, where `s` is the negative index
[@Cas08a, Theorem 1.2, p. 55]. -/
noncomputable def realHasseMinkowskiInvariant (L : FiniteFormCat ℝ ℝ)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm ℝ L).associated) : ℤ :=
  (diagonalPresentation L hL).hasseMinkowskiValue

/-- Every real diagonal presentation computes the canonical Hasse--Minkowski invariant. -/
theorem realHasseMinkowskiInvariant_eq
    (L : FiniteFormCat ℝ ℝ)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm ℝ L).associated)
    (d : DiagonalPresentation L hL) :
    d.hasseMinkowskiValue = realHasseMinkowskiInvariant L hL := by
  let d₀ := diagonalPresentation L hL
  rw [DiagonalPresentation.hasseMinkowskiValue,
    realHasseMinkowskiInvariant, DiagonalPresentation.hasseMinkowskiValue,
    hasseMinkowskiInvariantOfDiagonal_real,
    hasseMinkowskiInvariantOfDiagonal_real]
  congr 1
  apply negativeCoefficientPairs_card_eq_of_ncard_eq
  rw [← QuadraticForm.sigNeg_of_equiv_weightedSumSquares d.equivalent,
    ← QuadraticForm.sigNeg_of_equiv_weightedSumSquares d₀.equivalent]

/-- The real Hasse--Minkowski invariant is independent of diagonalization. -/
theorem real_isHasseMinkowskiInvariant
    (L : FiniteFormCat ℝ ℝ)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm ℝ L).associated) :
    IsHasseMinkowskiInvariant L hL (realHasseMinkowskiInvariant L hL) :=
  realHasseMinkowskiInvariant_eq L hL

/-- The real Hasse--Minkowski invariant is preserved by formed-module isomorphisms. -/
theorem realHasseMinkowskiInvariant_iso
    {L M : FiniteFormCat ℝ ℝ}
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm ℝ L).associated)
    (hM : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm ℝ M).associated)
    (e : L ≅ M) :
    realHasseMinkowskiInvariant L hL =
      realHasseMinkowskiInvariant M hM := by
  let dL := diagonalPresentation L hL
  let dM := diagonalPresentation M hM
  rw [← realHasseMinkowskiInvariant_eq L hL dL,
    ← realHasseMinkowskiInvariant_eq M hM dM,
    DiagonalPresentation.hasseMinkowskiValue,
    DiagonalPresentation.hasseMinkowskiValue,
    hasseMinkowskiInvariantOfDiagonal_real,
    hasseMinkowskiInvariantOfDiagonal_real]
  congr 1
  apply negativeCoefficientPairs_card_eq_of_ncard_eq
  rw [← QuadraticForm.sigNeg_of_equiv_weightedSumSquares dL.equivalent,
    ← QuadraticForm.sigNeg_of_equiv_weightedSumSquares dM.equivalent]
  exact QuadraticMap.Equivalent.sigNeg_eq
    (⟨finiteFormQuadraticIsometryEquiv ℝ e⟩ :
      QuadraticMap.Equivalent (finiteFormQuadraticForm ℝ L)
        (finiteFormQuadraticForm ℝ M))

/-- The determinant square class computed from a diagonal presentation. -/
noncomputable def DiagonalPresentation.determinantSquareClass
    {L : FiniteFormCat K K}
    {hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated}
    (d : DiagonalPresentation L hL) : FieldSquareClass K :=
  fieldSquareClass (∏ i, d.weights i)

/-- The discriminant of a weighted sum of squares is the product of its weights. -/
theorem weightedSumSquares_discr'
    {n : Type*} [Fintype n] [DecidableEq n]
    (w : n → K) :
    QuadraticForm.discr' (QuadraticMap.weightedSumSquares K w) = ∏ i, w i := by
  rw [QuadraticForm.discr']
  have hvalue (i : n) :
      QuadraticMap.weightedSumSquares K w (Pi.single i (1 : K)) = w i := by
    classical
    simp [QuadraticMap.weightedSumSquares_apply, Pi.single_apply, eq_comm]
  have hadd (i j : n) (hij : i ≠ j) :
      QuadraticMap.weightedSumSquares K w
          (Pi.single i (1 : K) + Pi.single j (1 : K)) =
        w i + w j := by
    classical
    rw [QuadraticMap.weightedSumSquares_apply]
    calc
      (∑ x, w x * (((Pi.single i (1 : K) : n → K) x +
          (Pi.single j (1 : K) : n → K) x) *
          ((Pi.single i (1 : K) : n → K) x +
          (Pi.single j (1 : K) : n → K) x))) =
          ∑ x, ((if i = x then w x else 0) + (if j = x then w x else 0)) := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hxi : i = x <;> by_cases hxj : j = x
            · exact (hij (hxi.trans hxj.symm)).elim
            · simp [hxi, hxj]
            · simp [hxi, hxj]
            · simp [hxi, hxj]
      _ = w i + w j := by
        rw [Finset.sum_add_distrib]
        simp
  have hmatrix :
      QuadraticForm.toMatrix' (QuadraticMap.weightedSumSquares K w) =
        Matrix.diagonal w := by
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [QuadraticForm.toMatrix'] using
        QuadraticMap.associated_eq_self_apply K
          (QuadraticMap.weightedSumSquares K w) (Pi.single i (1 : K)) |>.trans (hvalue i)
    · simp only [QuadraticForm.toMatrix', LinearMap.toMatrix₂'_apply,
        Matrix.diagonal_apply, hij, if_false]
      rw [QuadraticMap.associated_apply, hadd i j hij, hvalue i, hvalue j]
      simp
  rw [hmatrix, Matrix.det_diagonal]

/-- Equivalent nonsingular diagonal forms have the same determinant square class.

Cassels states this basis-independence when he defines the determinant of a quadratic form
modulo nonzero squares [@Cas08a, p. 55]. Mathlib's discriminant change formula supplies the
square factor produced by the change-of-basis determinant.
-/
theorem determinantSquareClass_eq_of_equivalent_weightedSumSquares
    {n : Type*} [Fintype n] [DecidableEq n]
    (w w' : n → Kˣ)
    (h : QuadraticMap.Equivalent
      (QuadraticMap.weightedSumSquares K w)
      (QuadraticMap.weightedSumSquares K w')) :
    fieldSquareClass (∏ i, w i) = fieldSquareClass (∏ i, w' i) := by
  let e := Classical.choice h
  let b := Pi.basisFun K n
  let δ : Kˣ := (e.toLinearEquiv.isUnit_det b b).unit
  have hform : QuadraticMap.weightedSumSquares K w =
      (QuadraticMap.weightedSumSquares K w').comp e.toLinearEquiv.toLinearMap := by
    ext x
    exact (e.map_app x).symm
  have hdet : (∏ i, (w i : K)) = (δ : K) ^ 2 * ∏ i, (w' i : K) := by
    have hdiscr := congrArg QuadraticForm.discr' hform
    rw [QuadraticForm.discr'_comp] at hdiscr
    change QuadraticForm.discr' (QuadraticMap.weightedSumSquares K
        (fun i ↦ (w i : K))) = _ * _ *
      QuadraticForm.discr' (QuadraticMap.weightedSumSquares K
        (fun i ↦ (w' i : K))) at hdiscr
    rw [weightedSumSquares_discr' (fun i ↦ (w i : K)),
      weightedSumSquares_discr' (fun i ↦ (w' i : K))] at hdiscr
    simpa [δ, b, pow_two] using hdiscr
  have hunits : (∏ i, w i) = δ ^ 2 * ∏ i, w' i := by
    ext
    simpa using hdet
  rw [hunits]
  change (QuotientGroup.mk' (Subgroup.square Kˣ))
      (δ ^ 2 * ∏ i, w' i) =
    (QuotientGroup.mk' (Subgroup.square Kˣ)) (∏ i, w' i)
  rw [map_mul, map_pow, modSquares_sq, one_mul]

/-- The determinant square class does not depend on the diagonal presentation. -/
theorem DiagonalPresentation.determinantSquareClass_eq
    {L : FiniteFormCat K K}
    {hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated}
    (d d' : DiagonalPresentation L hL) :
    d.determinantSquareClass = d'.determinantSquareClass := by
  apply determinantSquareClass_eq_of_equivalent_weightedSumSquares
  exact d.equivalent.symm.trans d'.equivalent

/-- The canonical determinant square class of a nondegenerate finite symmetric form. -/
noncomputable def finiteFormDeterminantSquareClass
    (L : FiniteFormCat K K)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated) : FieldSquareClass K :=
  (diagonalPresentation L hL).determinantSquareClass

/-- Every diagonal presentation computes the canonical determinant square class. -/
theorem finiteFormDeterminantSquareClass_eq
    (L : FiniteFormCat K K)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated)
    (d : DiagonalPresentation L hL) :
    finiteFormDeterminantSquareClass L hL = d.determinantSquareClass :=
  DiagonalPresentation.determinantSquareClass_eq _ _

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

/-- The canonical rank, determinant, and Hasse profile of a nondegenerate real form. -/
noncomputable def realFiniteFormProfile
    (L : FiniteFormCat ℝ ℝ)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm ℝ L).associated) : DiagonalFormProfile ℝ where
  rank := Module.finrank ℝ L.obj.carrier
  determinant := finiteFormDeterminantSquareClass L hL
  hasse := realHasseMinkowskiInvariant L hL

/-- Every real diagonal presentation computes the canonical profile. -/
theorem realFiniteFormProfile_eq
    (L : FiniteFormCat ℝ ℝ)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm ℝ L).associated)
    (d : DiagonalPresentation L hL) :
    realFiniteFormProfile L hL = d.profile := by
  unfold realFiniteFormProfile DiagonalPresentation.profile
  congr
  · exact finiteFormDeterminantSquareClass_eq L hL d
  · exact (realHasseMinkowskiInvariant_eq L hL d).symm

end LeanCategories.Lattices.Valued

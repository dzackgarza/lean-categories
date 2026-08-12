/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.WittCancellation
public import LeanCategories.Lattices.Valued.Hasse

/-!
# Invariance of the Hasse--Minkowski value

The Hasse--Minkowski value of a diagonal presentation depends only on the isometry class
of the form. The proof follows Cassels: a represented value can be moved to the leading
coefficient by changes that touch at most the first two coefficients, and Witt
cancellation then drops the rank.

Reference: Cassels, *Rational Quadratic Forms*, Lemma 2.2 [@Cas08a, p. 56].
-/

@[expose] public section

namespace LeanCategories.Lattices.Valued

open QuadraticMap
open LeanCategories.ForMathlib

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)] [HasBilinearHilbertSymbol K]

/-- The diagonal form attached to a tuple of unit weights. -/
noncomputable abbrev diagonalForm {n : ℕ} (w : Fin n → Kˣ) :
    QuadraticForm K (Fin n → K) :=
  weightedSumSquares K fun i => (w i : K)

omit [Invertible (2 : K)] [HasBilinearHilbertSymbol K] in
theorem coe_cons_units {n : ℕ} (a : Kˣ) (c : Fin n → Kˣ) :
    (fun i => ((Fin.cons a c : Fin (n + 1) → Kˣ) i : K)) =
      Fin.cons (a : K) fun i => (c i : K) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

omit [Invertible (2 : K)] [HasBilinearHilbertSymbol K] in
theorem diagonalForm_apply {n : ℕ} (w : Fin n → Kˣ) (x : Fin n → K) :
    diagonalForm w x = ∑ i, (w i : K) * (x i * x i) := by
  simp [QuadraticMap.weightedSumSquares_apply]

omit [Invertible (2 : K)] in
/-- A represented value can be taken as the leading coefficient.

If the diagonal form of `w` takes the nonzero value `a`, then `w` is equivalent to a tuple
with leading coefficient `a`, with the same Hasse--Minkowski value and the same determinant
square class. -/
theorem exists_cons_of_represents {n : ℕ} (w : Fin (n + 1) → Kˣ) (a : Kˣ)
    (x : Fin (n + 1) → K) (hx : diagonalForm w x = (a : K)) :
    ∃ c : Fin n → Kˣ,
      QuadraticMap.Equivalent (diagonalForm w) (diagonalForm (Fin.cons a c)) ∧
      hasseMinkowskiInvariantOfDiagonal w =
        hasseMinkowskiInvariantOfDiagonal (Fin.cons a c) ∧
      fieldSquareClass (∏ i, w i) = fieldSquareClass (a * ∏ i, c i) := by
  induction n generalizing a with
  | zero =>
    have hx0 : x 0 ≠ 0 := by
      intro h0
      apply Units.ne_zero a
      rw [← hx, diagonalForm_apply]
      simp [h0]
    have hval : a = w 0 * Units.mk0 (x 0) hx0 * Units.mk0 (x 0) hx0 := by
      apply Units.ext
      rw [← hx, diagonalForm_apply]
      simp [mul_assoc]
    refine ⟨Fin.elim0, ?_, ?_, ?_⟩
    · have hrescale :=
        equivalent_weightedSumSquares_rescale w fun _ => Units.mk0 (x 0) hx0
      have hfun : (fun i : Fin 1 => w i * (Units.mk0 (x 0) hx0 * Units.mk0 (x 0) hx0)) =
          Fin.cons a Fin.elim0 := by
        funext i
        fin_cases i
        simp [hval, mul_assoc]
      rw [hfun] at hrescale
      change QuadraticMap.Equivalent (weightedSumSquares K fun i => (w i : K))
        (weightedSumSquares K fun i => ((Fin.cons a Fin.elim0 : Fin 1 → Kˣ) i : K))
      rw [weightedSumSquares_units, weightedSumSquares_units]
      exact hrescale.symm
    · rw [hasseMinkowskiInvariantOfDiagonal_one, hasseMinkowskiInvariantOfDiagonal_one]
    · have hone : (∏ i : Fin 0, (Fin.elim0 i : Kˣ)) = 1 := by simp
      have hw : (∏ i : Fin (0 + 1), w i) = w 0 := by simp
      rw [hw, hone, mul_one, hval, mul_assoc, fieldSquareClass_mul_sq]
  | succ n ih =>
    obtain ⟨b, v, rfl⟩ : ∃ (b : Kˣ) (v : Fin (n + 1) → Kˣ), w = Fin.cons b v := by
      refine ⟨w 0, fun i => w i.succ, ?_⟩
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    have hsplit : (b : K) * (x 0 * x 0) +
        diagonalForm v (fun i => x i.succ) = (a : K) := by
      rw [← hx, diagonalForm_apply, diagonalForm_apply]
      conv_rhs => rw [Fin.sum_univ_succ]
      simp
    by_cases hx0 : x 0 = 0
    · have hsa : diagonalForm v (fun i => x i.succ) = (a : K) := by
        rw [← hsplit, hx0]
        ring
      obtain ⟨c', hequiv, hvalue, hdet⟩ := ih v a (fun i => x i.succ) hsa
      refine ⟨Fin.cons b c', ?_, ?_, ?_⟩
      · refine (?_ : QuadraticMap.Equivalent (diagonalForm (Fin.cons b v))
          (diagonalForm (Fin.cons b (Fin.cons a c')))).trans ?_
        · change QuadraticMap.Equivalent
            (weightedSumSquares K fun i => ((Fin.cons b v : Fin (n + 2) → Kˣ) i : K))
            (weightedSumSquares K fun i => ((Fin.cons b (Fin.cons a c') : Fin (n + 2) → Kˣ) i : K))
          simp only [coe_cons_units]
          have hequiv' : QuadraticMap.Equivalent
              (weightedSumSquares K fun i => (v i : K))
              (weightedSumSquares K (Fin.cons (a : K) fun i => (c' i : K))) := by
            simpa only [diagonalForm, coe_cons_units] using hequiv
          exact equivalent_cons_of_equivalent (b : K) _ _ hequiv'
        · change QuadraticMap.Equivalent
            (weightedSumSquares K fun i => ((Fin.cons b (Fin.cons a c') : Fin (n + 2) → Kˣ) i : K))
            (weightedSumSquares K fun i => ((Fin.cons a (Fin.cons b c') : Fin (n + 2) → Kˣ) i : K))
          simp only [coe_cons_units]
          exact equivalent_cons_cons_of_equivalent_two (b : K) (a : K) (a : K) (b : K)
            _ (equivalent_weightedSumSquares_two_swap (b : K) (a : K))
      · have step₁ : hasseMinkowskiInvariantOfDiagonal (Fin.cons b v) =
            hasseMinkowskiInvariantOfDiagonal (Fin.cons b (Fin.cons a c')) := by
          refine hasseMinkowskiInvariantOfDiagonal_cons_congr _ _ _ hvalue ?_
          rw [Fin.prod_cons]
          exact hdet
        have step₂ : hasseMinkowskiInvariantOfDiagonal (Fin.cons b (Fin.cons a c')) =
            hasseMinkowskiInvariantOfDiagonal (Fin.cons a (Fin.cons b c')) := by
          refine hasseMinkowskiInvariantOfDiagonal_cons_cons_congr _ _ _ _ _
            (hilbertSymbol_comm _ _) ?_
          rw [mul_comm]
        exact step₁.trans step₂
      · rw [Fin.prod_cons, Fin.prod_cons, fieldSquareClass_mul, fieldSquareClass_mul,
          hdet, fieldSquareClass_mul, fieldSquareClass_mul]
        simp [mul_left_comm]
    · by_cases hs0 : diagonalForm v (fun i => x i.succ) = 0
      · have hval : a = b * Units.mk0 (x 0) hx0 * Units.mk0 (x 0) hx0 := by
          apply Units.ext
          rw [← hsplit, hs0]
          simp [mul_assoc]
        refine ⟨v, ?_, ?_, ?_⟩
        · have hrescale := equivalent_weightedSumSquares_rescale (Fin.cons b v)
            (Fin.cons (Units.mk0 (x 0) hx0) (fun _ => 1) : Fin (n + 2) → Kˣ)
          have hfun :
              (fun i : Fin (n + 2) => (Fin.cons b v : Fin (n + 2) → Kˣ) i *
                  ((Fin.cons (Units.mk0 (x 0) hx0) (fun _ => 1) : Fin (n + 2) → Kˣ) i *
                    (Fin.cons (Units.mk0 (x 0) hx0) (fun _ => 1) : Fin (n + 2) → Kˣ) i)) =
                (Fin.cons a v : Fin (n + 2) → Kˣ) := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · simp [hval, mul_assoc]
            · simp
          rw [hfun] at hrescale
          change QuadraticMap.Equivalent
            (weightedSumSquares K fun i => ((Fin.cons b v : Fin (n + 2) → Kˣ) i : K))
            (weightedSumSquares K fun i => ((Fin.cons a v : Fin (n + 2) → Kˣ) i : K))
          rw [weightedSumSquares_units, weightedSumSquares_units]
          exact hrescale.symm
        · refine hasseMinkowskiInvariantOfDiagonal_cons_head_congr _ _ _ ?_
          rw [hval, mul_assoc, fieldSquareClass_mul_sq]
        · rw [Fin.prod_cons, fieldSquareClass_mul, fieldSquareClass_mul, hval,
            mul_assoc, fieldSquareClass_mul_sq]
      · obtain ⟨c', hequiv, hvalue, hdet⟩ :=
          ih v (Units.mk0 _ hs0) (fun i => x i.succ) rfl
        set S : Kˣ := Units.mk0 _ hs0 with hS
        have hrepr : (b : K) * (x 0 * x 0) + (S : K) * (1 * 1) = (a : K) := by
          rw [hS]
          simpa using hsplit
        have hbinary :
            QuadraticMap.Equivalent
              (weightedSumSquares K ![(b : K), (S : K)])
              (weightedSumSquares K ![(a : K), (b : K) * (S : K) * (a : K)]) :=
          equivalent_weightedSumSquares_two_of_repr (b : K) (S : K) (x 0) 1 (a : K)
            (Units.ne_zero a) hrepr
        have hbinaryUnits :
            QuadraticMap.Equivalent
              (weightedSumSquares K ![b, S])
              (weightedSumSquares K ![a, b * S * a]) := by
          have hleft : (fun i => ((![b, S] : Fin 2 → Kˣ) i : K)) =
              ![(b : K), (S : K)] := by
            funext i
            fin_cases i <;> simp
          have hright : (fun i => ((![a, b * S * a] : Fin 2 → Kˣ) i : K)) =
              ![(a : K), (b : K) * (S : K) * (a : K)] := by
            funext i
            fin_cases i <;> simp
          rw [← weightedSumSquares_units, ← weightedSumSquares_units, hleft, hright]
          exact hbinary
        refine ⟨Fin.cons (b * S * a) c', ?_, ?_, ?_⟩
        · refine (?_ : QuadraticMap.Equivalent (diagonalForm (Fin.cons b v))
            (diagonalForm (Fin.cons b (Fin.cons S c')))).trans ?_
          · change QuadraticMap.Equivalent
              (weightedSumSquares K fun i => ((Fin.cons b v : Fin (n + 2) → Kˣ) i : K))
              (weightedSumSquares K fun i =>
                ((Fin.cons b (Fin.cons S c') : Fin (n + 2) → Kˣ) i : K))
            simp only [coe_cons_units]
            have hequiv' : QuadraticMap.Equivalent
                (weightedSumSquares K fun i => (v i : K))
                (weightedSumSquares K (Fin.cons (S : K) fun i => (c' i : K))) := by
              simpa only [diagonalForm, coe_cons_units] using hequiv
            exact equivalent_cons_of_equivalent (b : K) _ _ hequiv'
          · change QuadraticMap.Equivalent
              (weightedSumSquares K fun i =>
                ((Fin.cons b (Fin.cons S c') : Fin (n + 2) → Kˣ) i : K))
              (weightedSumSquares K fun i =>
                ((Fin.cons a (Fin.cons (b * S * a) c') : Fin (n + 2) → Kˣ) i : K))
            simp only [coe_cons_units]
            exact equivalent_cons_cons_of_equivalent_two (b : K) (S : K) (a : K)
              ((b : K) * (S : K) * (a : K)) _ hbinary
        · have step₁ : hasseMinkowskiInvariantOfDiagonal (Fin.cons b v) =
              hasseMinkowskiInvariantOfDiagonal (Fin.cons b (Fin.cons S c')) := by
            refine hasseMinkowskiInvariantOfDiagonal_cons_congr _ _ _ hvalue ?_
            rw [Fin.prod_cons]
            exact hdet
          have step₂ : hasseMinkowskiInvariantOfDiagonal (Fin.cons b (Fin.cons S c')) =
              hasseMinkowskiInvariantOfDiagonal
                (Fin.cons a (Fin.cons (b * S * a) c')) := by
            refine hasseMinkowskiInvariantOfDiagonal_cons_cons_congr _ _ _ _ _
              (hilbertSymbol_eq_of_equivalent_weightedSumSquares_two _ _ hbinaryUnits) ?_
            rw [show a * (b * S * a) = b * S * (a * a) by
              simp [mul_comm, mul_assoc, mul_left_comm], fieldSquareClass_mul_sq]
          exact step₁.trans step₂
        · rw [Fin.prod_cons, Fin.prod_cons, fieldSquareClass_mul, fieldSquareClass_mul,
            hdet, fieldSquareClass_mul, fieldSquareClass_mul, fieldSquareClass_mul,
            fieldSquareClass_mul]
          rw [show fieldSquareClass a *
              (fieldSquareClass b * fieldSquareClass S * fieldSquareClass a *
                fieldSquareClass (∏ i, c' i)) =
            (fieldSquareClass a * fieldSquareClass a) *
              (fieldSquareClass b * (fieldSquareClass S *
                fieldSquareClass (∏ i, c' i))) by
            simp [mul_comm, mul_assoc, mul_left_comm],
            ← pow_two, modSquares_sq, one_mul]

omit [Invertible (2 : K)] [HasBilinearHilbertSymbol K] in
/-- The leading coefficient is represented by its own diagonal form. -/
theorem diagonalForm_single {n : ℕ} (w : Fin (n + 1) → Kˣ) :
    diagonalForm w (Pi.single 0 1) = (w 0 : K) := by
  classical
  rw [diagonalForm_apply]
  simp [Pi.single_apply, Finset.sum_ite_eq']

/-- The Hasse--Minkowski value depends only on the isometry class of the diagonal form.

This is Cassels's Lemma 2.2 [@Cas08a, p. 56]: the value computed from a diagonal
presentation is an invariant of the form it presents. -/
theorem hasseMinkowskiInvariantOfDiagonal_eq_of_equivalent {n : ℕ} (w w' : Fin n → Kˣ)
    (h : QuadraticMap.Equivalent (diagonalForm w) (diagonalForm w')) :
    hasseMinkowskiInvariantOfDiagonal w = hasseMinkowskiInvariantOfDiagonal w' := by
  induction n with
  | zero => simp [hasseMinkowskiInvariantOfDiagonal]
  | succ n ih =>
    obtain ⟨b, v, rfl⟩ : ∃ (b : Kˣ) (v : Fin n → Kˣ), w' = Fin.cons b v := by
      refine ⟨w' 0, fun i => w' i.succ, ?_⟩
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    obtain ⟨e⟩ := h
    have hb : ((Fin.cons b v : Fin (n + 1) → Kˣ) 0 : K) = (b : K) := by simp
    have hrepr : diagonalForm w (e.symm (Pi.single 0 1)) = (b : K) := by
      rw [← hb, ← diagonalForm_single (Fin.cons b v)]
      conv_rhs => rw [← e.apply_symm_apply (Pi.single 0 1)]
      exact (e.map_app _).symm
    obtain ⟨c, hequiv, hvalue, hdet⟩ :=
      exists_cons_of_represents w b (e.symm (Pi.single 0 1)) hrepr
    have hcancel : QuadraticMap.Equivalent (diagonalForm c) (diagonalForm v) := by
      have hchain : QuadraticMap.Equivalent (diagonalForm (Fin.cons b c))
          (diagonalForm (Fin.cons b v)) := hequiv.symm.trans ⟨e⟩
      have hchain' : QuadraticMap.Equivalent
          (weightedSumSquares K (Fin.cons (b : K) fun i => (c i : K)))
          (weightedSumSquares K (Fin.cons (b : K) fun i => (v i : K))) := by
        simpa only [diagonalForm, coe_cons_units] using hchain
      exact equivalent_tail_of_equivalent b c v hchain'
    have hdetv : fieldSquareClass (∏ i, c i) = fieldSquareClass (∏ i, v i) := by
      refine determinantSquareClass_eq_of_equivalent_weightedSumSquares c v ?_
      rw [← weightedSumSquares_units, ← weightedSumSquares_units]
      exact hcancel
    refine hvalue.trans ?_
    exact hasseMinkowskiInvariantOfDiagonal_cons_congr b c v (ih c v hcancel) hdetv

section Presentation

variable {L : FiniteFormCat K K}
  {hL : LinearMap.SeparatingLeft (finiteFormQuadraticForm K L).associated}

/-- Any two diagonal presentations of one form compute the same value. -/
theorem DiagonalPresentation.hasseMinkowskiValue_eq (d d' : DiagonalPresentation L hL) :
    d.hasseMinkowskiValue = d'.hasseMinkowskiValue := by
  refine hasseMinkowskiInvariantOfDiagonal_eq_of_equivalent d.weights d'.weights ?_
  rw [diagonalForm, diagonalForm, weightedSumSquares_units, weightedSumSquares_units]
  exact d.equivalent.symm.trans d'.equivalent

/-- The canonical Hasse--Minkowski invariant of a nondegenerate finite symmetric form. -/
noncomputable def hasseMinkowskiInvariant (L : FiniteFormCat K K)
    (hL : LinearMap.SeparatingLeft (finiteFormQuadraticForm K L).associated) : ℤ :=
  (diagonalPresentation L hL).hasseMinkowskiValue

/-- Every diagonal presentation computes the canonical invariant. -/
theorem hasseMinkowskiInvariant_eq (d : DiagonalPresentation L hL) :
    d.hasseMinkowskiValue = hasseMinkowskiInvariant L hL :=
  d.hasseMinkowskiValue_eq _

/-- The canonical value is an invariant in the sense of `IsHasseMinkowskiInvariant`. -/
theorem isHasseMinkowskiInvariant_hasseMinkowskiInvariant :
    IsHasseMinkowskiInvariant L hL (hasseMinkowskiInvariant L hL) :=
  fun d => hasseMinkowskiInvariant_eq d

end Presentation

end LeanCategories.Lattices.Valued

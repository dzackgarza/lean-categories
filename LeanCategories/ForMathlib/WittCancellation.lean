/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.QuadraticReflection
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Witt cancellation

Cancelling a common nonzero one-dimensional summand from an isometry of quadratic forms.
The proof moves the distinguished vector of the target onto the one of the source by a
reflection, after which the isometry carries one orthogonal complement onto the other.

Reference: Lam, *Introduction to Quadratic Forms over Fields*, Chapter I, Theorem 4.2.
-/

@[expose] public section

namespace LeanCategories.ForMathlib

open QuadraticMap

universe u v w

variable {K : Type u} [Field K] [Invertible (2 : K)]
variable {W : Type v} {W' : Type w}
variable [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W']

/-- The one-dimensional form `x ↦ a * x ^ 2`. -/
noncomputable def lineForm (a : K) : QuadraticForm K K :=
  a • QuadraticMap.sq

omit [Invertible (2 : K)] in
@[simp]
theorem lineForm_apply (a x : K) : lineForm a x = a * (x * x) := by
  simp [lineForm, QuadraticMap.sq]

omit [Invertible (2 : K)] in
theorem polar_prod_lineForm (a : K) (q : QuadraticForm K W) (s t : K) (y z : W) :
    polar ((lineForm a).prod q) (s, y) (t, z) =
      a * (2 * (s * t)) + polar q y z := by
  simp only [QuadraticMap.polar, QuadraticMap.prod_apply, lineForm_apply, Prod.fst_add,
    Prod.snd_add]
  ring

/-- The first coordinate of the image of a vector orthogonal to the distinguished line. -/
theorem fst_eq_zero_of_map_eq {a : K} (ha : a ≠ 0) {q : QuadraticForm K W}
    {q' : QuadraticForm K W'}
    (ψ : ((lineForm a).prod q).IsometryEquiv ((lineForm a).prod q'))
    (hψ : ψ (1, 0) = (1, 0)) (y : W) : (ψ (0, y)).1 = 0 := by
  have hpolar : ∀ x z, polar ((lineForm a).prod q') (ψ x) (ψ z) =
      polar ((lineForm a).prod q) x z := by
    intro x z
    simp only [QuadraticMap.polar, ← ψ.map_app, ← map_add]
  have h := hpolar (0, y) (1, 0)
  rw [hψ, polar_prod_lineForm, polar_prod_lineForm] at h
  simp only [polar_zero_right, add_zero, mul_one, mul_zero] at h
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  rcases mul_eq_zero.mp h with hcase | hcase
  · exact absurd hcase ha
  · rcases mul_eq_zero.mp hcase with hcase' | hcase'
    · exact absurd hcase' h2
    · exact hcase'

/-- A vector of the distinguished line maps into the distinguished line. -/
theorem map_inr_eq {a : K} (ha : a ≠ 0) {q : QuadraticForm K W} {q' : QuadraticForm K W'}
    (ψ : ((lineForm a).prod q).IsometryEquiv ((lineForm a).prod q'))
    (hψ : ψ (1, 0) = (1, 0)) (y : W) : ψ (0, y) = (0, (ψ (0, y)).2) :=
  Prod.ext (fst_eq_zero_of_map_eq ha ψ hψ y) rfl

omit [Invertible (2 : K)] in
/-- An isometry fixing a vector fixes it in the other direction as well. -/
theorem symm_apply_eq_of_apply_eq {a : K} {q : QuadraticForm K W}
    {q' : QuadraticForm K W'}
    (ψ : ((lineForm a).prod q).IsometryEquiv ((lineForm a).prod q'))
    (hψ : ψ (1, 0) = (1, 0)) : ψ.symm (1, 0) = (1, 0) := by
  conv_lhs => rw [← hψ]
  exact ψ.toLinearEquiv.symm_apply_apply (1, 0)

/-- An isometry fixing the distinguished vector restricts to the complements. -/
noncomputable def restrictComplement {a : K} (ha : a ≠ 0) {q : QuadraticForm K W}
    {q' : QuadraticForm K W'}
    (ψ : ((lineForm a).prod q).IsometryEquiv ((lineForm a).prod q'))
    (hψ : ψ (1, 0) = (1, 0)) : q.IsometryEquiv q' where
  toFun y := (ψ (0, y)).2
  invFun z := (ψ.symm (0, z)).2
  map_add' y z := by
    have h := ψ.toLinearEquiv.map_add ((0 : K), y) ((0 : K), z)
    simp only [Prod.mk_add_mk, add_zero] at h
    exact congrArg Prod.snd h
  map_smul' c y := by
    have h := ψ.toLinearEquiv.map_smul c ((0 : K), y)
    simp only [Prod.smul_mk, smul_zero] at h
    exact congrArg Prod.snd h
  left_inv y := by
    change (ψ.symm (0, (ψ (0, y)).2)).2 = y
    rw [← map_inr_eq ha ψ hψ y]
    simp
  right_inv z := by
    change (ψ ((0 : K), (ψ.symm (0, z)).2)).2 = z
    rw [← map_inr_eq ha ψ.symm (symm_apply_eq_of_apply_eq ψ hψ) z]
    simp
  map_app' y := by
    have hval := ψ.map_app ((0 : K), y)
    rw [map_inr_eq ha ψ hψ y] at hval
    simpa using hval

/-- Witt cancellation for a one-dimensional summand of nonzero value.

An isometry of `⟨a⟩ ⊥ q` with `⟨a⟩ ⊥ q'` gives an isometry of `q` with `q'`. -/
noncomputable def isometryEquivOfProdLineForm {a : K} (ha : a ≠ 0)
    {q : QuadraticForm K W} {q' : QuadraticForm K W'}
    (h : ((lineForm a).prod q).IsometryEquiv ((lineForm a).prod q')) :
    q.IsometryEquiv q' :=
  let hex := exists_isometryEquiv_apply_eq ((lineForm a).prod q') (h (1, 0)) (1, 0)
    (by rw [h.map_app]; simpa using ha) (by rw [h.map_app]; simp)
  restrictComplement ha (h.trans hex.choose)
    (show hex.choose (h (1, 0)) = (1, 0) from hex.choose_spec)

section Diagonal

/-- Splitting the first coefficient off a diagonal form. -/
noncomputable def prodLineFormIsometry {n : ℕ} (w : Fin (n + 1) → K) :
    ((lineForm (w 0)).prod
        (weightedSumSquares K fun i : Fin n => w i.succ)).IsometryEquiv
      (weightedSumSquares K w) where
  toLinearEquiv := Fin.consLinearEquiv K fun _ => K
  map_app' x := by
    simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_succ,
      Fin.consLinearEquiv, Fin.consEquiv, QuadraticMap.prod_apply]

/-- Witt cancellation of the leading coefficient of a diagonal form. -/
theorem equivalent_tail_of_equivalent {n : ℕ} (a : Kˣ) (w w' : Fin n → Kˣ)
    (h : QuadraticMap.Equivalent (weightedSumSquares K (Fin.cons (a : K) fun i => (w i : K)))
      (weightedSumSquares K (Fin.cons (a : K) fun i => (w' i : K)))) :
    QuadraticMap.Equivalent (weightedSumSquares K fun i => (w i : K))
      (weightedSumSquares K fun i => (w' i : K)) := by
  obtain ⟨e⟩ := h
  have hsplit : ∀ v : Fin n → Kˣ,
      ((lineForm (a : K)).prod
          (weightedSumSquares K fun i => (v i : K))).IsometryEquiv
        (weightedSumSquares K (Fin.cons (a : K) fun i => (v i : K))) := by
    intro v
    have h0 : (Fin.cons (a : K) (fun i => (v i : K)) : Fin (n + 1) → K) 0 = (a : K) := by
      simp
    have hsucc :
        (fun i : Fin n => (Fin.cons (a : K) (fun i => (v i : K)) : Fin (n + 1) → K) i.succ) =
          fun i => (v i : K) := by
      funext i
      simp
    have := prodLineFormIsometry (K := K) (Fin.cons (a : K) fun i => (v i : K))
    rwa [h0, hsucc] at this
  exact ⟨isometryEquivOfProdLineForm (Units.ne_zero a)
    (((hsplit w).trans e).trans (hsplit w').symm)⟩

end Diagonal

end LeanCategories.ForMathlib

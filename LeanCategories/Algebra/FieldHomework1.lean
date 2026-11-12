/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# The correction to Field Homework 1, problem 1(a)

Card `P-FHW1-01` of the qualifying-exam corpus.  Source: Field Homework 1,
problem 1(a), as transcribed in the new-qual-site collection
`SRC-FIELD-HOMEWORK-1`.  Certificate: new-qual-site `proofs/cards/
FieldHomework1.lean` at main `16c09abaa4`.

The sheet prints: α ∈ F is algebraic over K if and only if F contains a
finite-dimensional K-subspace L with α·L ⊆ L.

That is false as printed, because L = ⊥ satisfies the printed hypothesis for
every α (`printed_hypothesis_holds_for_bot`).  The corrected statement adds
`L ≠ 0`; this module certifies both directions of the corrected statement:

* `isAlgebraic_of_stable_ne_bot`;
* `exists_stable_finiteDimensional_of_isAlgebraic`.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): `isAlgebraic_of_stable_ne_bot` (corpus: 0 hits), "algebraic stable
subspace multiplication" (corpus: 32 files, generic; Mathlib has
`isAlgebraic_iff` characterizations via subalgebra tops, not the nonzero stable
subspace form certified here).  Route: written — the stability characterization
is the card's settled proof.
-/

open Polynomial

set_option linter.style.haveILetI false

namespace LeanCategories.Algebra.FieldHomework1

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The printed hypothesis of problem 1(a) holds with `L = ⊥` for every `α`: the
refutation of the statement as printed. -/
theorem printed_hypothesis_holds_for_bot (α : F) :
    FiniteDimensional K (⊥ : Submodule K F) ∧ ∀ x ∈ (⊥ : Submodule K F), α * x ∈ (⊥ : Submodule K F) := by
  refine ⟨?_, ?_⟩
  · rw [← Submodule.span_empty]
    exact Module.Finite.span_of_finite K (Set.finite_empty)
  · intro x hx
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, mul_zero]

/-- Converse of the corrected statement: a nonzero finite-dimensional subspace of `F`
stable under multiplication by `α` forces `α` to be algebraic over `K`. -/
theorem isAlgebraic_of_stable_ne_bot {α : F} {L : Submodule K F} (hL : L ≠ ⊥)
    (hfin : FiniteDimensional K L) (hstable : ∀ x ∈ L, α * x ∈ L) : IsAlgebraic K α := by
  classical
  haveI := hfin
  obtain ⟨v, hvL, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
  have hmem : ∀ i : ℕ, α ^ i * v ∈ L := by
    intro i
    induction i with
    | zero => simpa using hvL
    | succ i ih =>
      have hstep : α * (α ^ i * v) ∈ L := hstable _ ih
      simpa [pow_succ', mul_assoc] using hstep
  set n := Module.finrank K L with hn
  let y : Fin (n + 1) → L := fun i => ⟨α ^ (i : ℕ) * v, hmem (i : ℕ)⟩
  have hdep : ¬ LinearIndependent K y := by
    intro hli
    have hle : Fintype.card (Fin (n + 1)) ≤ Module.finrank K L := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hle
    omega
  have hdep' : ∃ c : Fin (n + 1) → K, (∑ i, c i • y i) = 0 ∧ ∃ i, c i ≠ 0 := by
    by_contra h
    apply hdep
    rw [Fintype.linearIndependent_iff]
    intro l hl
    by_contra hne
    exact h ⟨l, hl, not_forall.mp hne⟩
  obtain ⟨c, hcsum, i0, hi0⟩ := hdep'
  have hv : (∑ i : Fin (n + 1), algebraMap K F (c i) * (α ^ (i : ℕ) * v)) = 0 := by
    have := congrArg (Subtype.val) hcsum
    simpa [y, Algebra.smul_def] using this
  have hfactor :
      (∑ i : Fin (n + 1), algebraMap K F (c i) * α ^ (i : ℕ)) * v
        = ∑ i : Fin (n + 1), algebraMap K F (c i) * (α ^ (i : ℕ) * v) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hzero : (∑ i : Fin (n + 1), algebraMap K F (c i) * α ^ (i : ℕ)) = 0 := by
    have hmul : (∑ i : Fin (n + 1), algebraMap K F (c i) * α ^ (i : ℕ)) * v = 0 := by
      rw [hfactor, hv]
    exact (mul_eq_zero.mp hmul).resolve_right hv0
  refine ⟨∑ i : Fin (n + 1), C (c i) * X ^ (i : ℕ), ?_, ?_⟩
  · intro hp
    have hcoeff := congrArg (fun p : K[X] => p.coeff (i0 : ℕ)) hp
    simp only [Polynomial.coeff_zero] at hcoeff
    rw [Polynomial.finsetSum_coeff] at hcoeff
    have hsingle :
        ∑ i : Fin (n + 1), (C (c i) * X ^ (i : ℕ) : K[X]).coeff (i0 : ℕ) = c i0 := by
      rw [Finset.sum_eq_single i0]
      · simp
      · intro i _ hne
        have hne'' : (i0 : ℕ) ≠ (i : ℕ) := fun h => hne (Fin.ext h.symm)
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne'']
      · intro h
        exact absurd (Finset.mem_univ i0) h
    rw [hsingle] at hcoeff
    exact hi0 hcoeff
  · have hval :
        aeval α (∑ i : Fin (n + 1), C (c i) * X ^ (i : ℕ))
          = ∑ i : Fin (n + 1), algebraMap K F (c i) * α ^ (i : ℕ) := by
      simp [map_sum]
    rw [hval, hzero]

/-- Forward direction of the corrected statement: an algebraic `α` admits a nonzero
finite-dimensional subspace stable under multiplication by `α`, namely `K[α]`. -/
theorem exists_stable_finiteDimensional_of_isAlgebraic {α : F} (h : IsAlgebraic K α) :
    ∃ L : Submodule K F, L ≠ ⊥ ∧ FiniteDimensional K L ∧ ∀ x ∈ L, α * x ∈ L := by
  classical
  have hint : IsIntegral K α := isAlgebraic_iff_isIntegral.mp h
  let B : Subalgebra K F := Algebra.adjoin K {α}
  have hfin : Module.Finite K B := Algebra.finite_adjoin_simple_of_isIntegral hint
  refine ⟨B.toSubmodule, ?_, hfin, ?_⟩
  · intro hbot
    have h1 : (1 : F) ∈ B := B.one_mem
    have : (1 : F) ∈ (⊥ : Submodule K F) := by
      rw [← hbot]
      exact h1
    rw [Submodule.mem_bot] at this
    exact one_ne_zero this
  · intro x hx
    have hxB : x ∈ B := hx
    exact B.mul_mem (Algebra.subset_adjoin (Set.mem_singleton α)) hxB

end LeanCategories.Algebra.FieldHomework1

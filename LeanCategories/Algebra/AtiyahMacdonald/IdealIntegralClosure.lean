/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal

@[expose] public section

namespace LeanCategories.Algebra.AtiyahMacdonald

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Atiyah–Macdonald, Chapter 5, p. 63 (FC04-C05-U023): `x` satisfies a monic equation
whose nonleading coefficients lie in `I`.

This is the convention of the admitted 1969 source, not the stronger ideal-power
condition of Stacks Project Tag 00H2. In particular, over the base ring itself this
predicate gives the radical, as proved below. -/
def IsIntegralOverIdeal (I : Ideal R) (x : S) : Prop :=
  ∃ p : Polynomial R, p.Monic ∧ Polynomial.aeval x p = 0 ∧
    ∀ i ≠ p.natDegree, p.coeff i ∈ I

/-- Atiyah–Macdonald, Chapter 5 (FC04-C05-U024): the integral closure of `I` in an
ambient `R`-algebra is the set of elements integral over `I`. -/
def integralClosureOfIdeal (I : Ideal R) : Set S :=
  {x | IsIntegralOverIdeal I x}

/-- The source's coefficient condition implies a power lies in the extended ideal. -/
theorem IsIntegralOverIdeal.mem_radical_map {I : Ideal R} {x : S}
    (h : IsIntegralOverIdeal I x) : x ∈ (I.map (algebraMap R S)).radical := by
  obtain ⟨p, hp, hx, hcoeff⟩ := h
  refine ⟨p.natDegree, ?_⟩
  have hsum : (∑ i ∈ Finset.range p.natDegree, algebraMap R S (p.coeff i) * x ^ i) ∈
      I.map (algebraMap R S) :=
    (I.map (algebraMap R S)).sum_mem fun i hi => Ideal.mul_mem_right _ _
      (Ideal.mem_map_of_mem _ (hcoeff i (Nat.ne_of_lt (Finset.mem_range.mp hi))))
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ,
    hp.coeff_natDegree, map_one, one_mul] at hx
  rw [eq_neg_of_add_eq_zero_right hx]
  exact (I.map (algebraMap R S)).neg_mem hsum

/-- Source integrality over an ideal of the base ring is precisely radical membership. -/
theorem isIntegralOverIdeal_iff_mem_radical (I : Ideal R) (x : R) :
    IsIntegralOverIdeal I x ↔ x ∈ I.radical := by
  constructor
  · intro h
    simpa using h.mem_radical_map
  · rintro ⟨n, hn⟩
    have hpow : x ^ (n + 1) ∈ I := by
      simpa only [pow_succ] using I.mul_mem_right x hn
    refine ⟨Polynomial.X ^ (n + 1) - Polynomial.C (x ^ (n + 1)),
      Polynomial.monic_X_pow_sub_C _ (Nat.succ_ne_zero n), by simp, ?_⟩
    intro i hi
    by_cases hR : Subsingleton R
    · have : Subsingleton R := hR
      have hz : (Polynomial.X ^ (n + 1) - Polynomial.C (x ^ (n + 1))).coeff i = (0 : R) :=
        Subsingleton.elim _ _
      exact hz.symm ▸ I.zero_mem
    · let : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
      have hin : i ≠ n + 1 := by simpa only [Polynomial.natDegree_X_pow_sub_C] using hi
      by_cases hi0 : i = 0
      · subst i
        simpa only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hin,
          Polynomial.coeff_C_zero, zero_sub] using I.neg_mem hpow
      · simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hin,
          Polynomial.coeff_C, if_neg hi0, sub_self, Submodule.zero_mem]

/-- The base-ring specialization of FC04-C05-U024 agrees with the existing ideal radical. -/
theorem integralClosureOfIdeal_self (I : Ideal R) :
    integralClosureOfIdeal (S := R) I = (I.radical : Set R) := by
  ext x
  exact isIntegralOverIdeal_iff_mem_radical I x

-- The admitted convention includes 2 over (4), not just members of (4).
example : IsIntegralOverIdeal (Ideal.span ({4} : Set ℤ)) (2 : ℤ) := by
  rw [isIntegralOverIdeal_iff_mem_radical]
  exact ⟨2, by norm_num [Ideal.mem_span_singleton]⟩

example : (2 : ℤ) ∉ Ideal.span ({4} : Set ℤ) := by
  norm_num [Ideal.mem_span_singleton]

-- Omitting the coefficient restriction altogether would incorrectly admit 1.
example : ¬ IsIntegralOverIdeal (Ideal.span ({4} : Set ℤ)) (1 : ℤ) := by
  rw [isIntegralOverIdeal_iff_mem_radical]
  rintro ⟨n, hn⟩
  norm_num [Ideal.mem_span_singleton] at hn

end LeanCategories.Algebra.AtiyahMacdonald

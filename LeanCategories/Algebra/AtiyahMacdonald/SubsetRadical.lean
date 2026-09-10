/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

namespace LeanCategories.Algebra

universe u

variable {R : Type u} [CommRing R]

/-- Atiyah–Macdonald, Chapter 1 (FC04-C01-U052): the radical of an arbitrary subset
`E` consists of the elements whose positive power belongs to `E`. Unlike the radical of an
ideal, this is only a set in general. -/
def subsetRadical (E : Set R) : Set R :=
  {x | ∃ n : ℕ, x ^ (n + 1) ∈ E}

@[simp]
theorem mem_subsetRadical {E : Set R} {x : R} :
    x ∈ subsetRadical E ↔ ∃ n : ℕ, x ^ (n + 1) ∈ E :=
  Iff.rfl

/-- The arbitrary-subset radical commutes with arbitrary unions, as in FC04-C01-U052. -/
theorem subsetRadical_iUnion {ι : Sort*} (E : ι → Set R) :
    subsetRadical (⋃ i, E i) = ⋃ i, subsetRadical (E i) := by
  ext x
  simp only [subsetRadical, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨n, i, hi⟩
    exact ⟨i, n, hi⟩
  · rintro ⟨i, n, hi⟩
    exact ⟨n, i, hi⟩

/-- On ideals the positive-power convention agrees with Mathlib's radical. -/
theorem subsetRadical_coe_ideal (I : Ideal R) :
    subsetRadical (I : Set R) = (I.radical : Set R) := by
  ext x
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, hn⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change x ^ (n + 1) ∈ I
    simpa only [pow_succ] using I.mul_mem_right x hn

-- The source permits arbitrary subsets, not just ideals or multiplicatively closed sets.
example : (2 : ℤ) ∈ subsetRadical ({4} : Set ℤ) := ⟨1, by norm_num⟩

-- This radical cannot be an ideal: unlike an ideal, it does not contain zero.
example : ¬∃ I : Ideal ℤ, (I : Set ℤ) = subsetRadical ({4} : Set ℤ) := by
  rintro ⟨I, hI⟩
  have h0 : (0 : ℤ) ∈ subsetRadical ({4} : Set ℤ) := hI ▸ I.zero_mem
  simp [subsetRadical] at h0

-- Allowing the zeroth power for arbitrary subsets would incorrectly admit this element.
example : (2 : ℤ) ∉ subsetRadical ({1} : Set ℤ) := by
  rintro ⟨n, hn⟩
  have hpow : (1 : ℤ) < 2 ^ (n + 1) := one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero n)
  exact (ne_of_gt hpow) hn

end LeanCategories.Algebra

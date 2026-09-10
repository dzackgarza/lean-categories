/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.SumTwoSquares
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Data.Nat.Prime.Int

/-!
# Rational prime ideals in the Gaussian integers

Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), printed p. 10,
FC04-C01-U058. The integer prime 2 ramifies, primes congruent to 1 modulo 4 split
into distinct conjugate prime ideals, and primes congruent to 3 modulo 4 remain prime.

The ring, norm, ideal extension and Fermat sum-of-two-squares theorem are Mathlib's.
The proofs below establish the ideal factorizations, their distinctness, and uniqueness
of norm-prime factors up to units and conjugation. In particular, the factorization
identity alone is not used as evidence that its two factors are distinct.
-/

@[expose] public section

namespace GaussianInt

/-- A Gaussian integer whose norm is prime is prime. -/
lemma prime_of_prime_norm {z : GaussianInt} (hn : Prime z.norm) : Prime z := by
  apply irreducible_iff_prime.mp
  refine ⟨fun h => hn.not_isUnit ((Zsqrtd.isUnit_iff_norm_isUnit z).mp h), ?_⟩
  intro a b hab
  have hm : z.norm = a.norm * b.norm := by rw [hab, Zsqrtd.norm_mul]
  exact (hn.irreducible.isUnit_or_isUnit hm).imp
    (Zsqrtd.isUnit_iff_norm_isUnit a).mpr (Zsqrtd.isUnit_iff_norm_isUnit b).mpr

/-- Conjugate Gaussian integers of odd prime norm are not associates. -/
lemma not_associated_star_of_prime_norm {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {z : GaussianInt} (hn : z.norm = (p : ℤ)) : ¬ Associated z (star z) := by
  intro h
  have hip : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hn2 : ¬ (p : ℤ) ∣ 2 := by
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (Int.natCast_dvd_natCast.mp hd))
  have hna : (z + star z).norm = (2 * z.re) ^ 2 := by
    simp [Zsqrtd.norm_def]
    ring
  have hnb : (z - star z).norm = (2 * z.im) ^ 2 := by
    simp [Zsqrtd.norm_def]
    ring
  have ha : (p : ℤ) ∣ z.re := by
    have hd := map_dvd (Zsqrtd.normMonoidHom (d := -1)) (dvd_add (dvd_refl z) h.dvd)
    change z.norm ∣ (z + star z).norm at hd
    rw [hn, hna] at hd
    exact (hip.dvd_or_dvd (hip.dvd_of_dvd_pow hd)).resolve_left hn2
  have hb : (p : ℤ) ∣ z.im := by
    have hd := map_dvd (Zsqrtd.normMonoidHom (d := -1)) (dvd_sub (dvd_refl z) h.dvd)
    change z.norm ∣ (z - star z).norm at hd
    rw [hn, hnb] at hd
    exact (hip.dvd_or_dvd (hip.dvd_of_dvd_pow hd)).resolve_left hn2
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  have he : (p : ℤ) * 1 = (p : ℤ) * ((p : ℤ) * (a ^ 2 + b ^ 2)) := by
    calc
      (p : ℤ) * 1 = z.norm := by rw [hn, mul_one]
      _ = (p : ℤ) * ((p : ℤ) * (a ^ 2 + b ^ 2)) := by
        rw [Zsqrtd.norm_def, ha, hb]
        ring
  exact hip.not_dvd_one ⟨_, mul_left_cancel₀ hip.ne_zero he⟩

/-- A rational prime congruent to 1 modulo 4 splits into distinct conjugate prime ideals.
The chosen generator has norm `p`, explicitly relating splitting to a sum of two squares. -/
lemma exists_prime_ideal_factorization_of_mod_four_eq_one {p : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 1) :
    ∃ z : GaussianInt, z.norm = (p : ℤ) ∧
      (Ideal.span ({z} : Set GaussianInt)).IsPrime ∧
      (Ideal.span ({star z} : Set GaussianInt)).IsPrime ∧
      Ideal.span ({z} : Set GaussianInt) ≠ Ideal.span {star z} ∧
      (Ideal.span ({(p : ℤ)} : Set ℤ)).map (Int.castRingHom GaussianInt) =
        Ideal.span ({z} : Set GaussianInt) * Ideal.span {star z} := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  let z : GaussianInt := ⟨a, b⟩
  have hn : z.norm = (p : ℤ) := by
    have hcast : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (p : ℤ) := by exact_mod_cast hab
    dsimp [z, Zsqrtd.norm]
    nlinarith
  have hip : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hz : Prime z := prime_of_prime_norm (hn ▸ hip)
  have hs : Prime (star z) := prime_of_prime_norm (by simpa only [Zsqrtd.norm_conj, hn] using hip)
  refine ⟨z, hn, Ideal.isPrime_span_singleton_of_prime hz,
    Ideal.isPrime_span_singleton_of_prime hs, ?_, ?_⟩
  · exact fun h => not_associated_star_of_prime_norm hp (by omega) hn
      (Ideal.span_singleton_eq_span_singleton.mp h)
  · rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton,
      ← Zsqrtd.norm_eq_mul_conj, hn]
    simp

/-- The extended ideal `(2)` is the square of the prime ideal `(1 + i)`. -/
lemma ramification_two :
    (Ideal.span ({(2 : ℤ)} : Set ℤ)).map (Int.castRingHom GaussianInt) =
      Ideal.span ({(⟨1, 1⟩ : GaussianInt)} : Set GaussianInt) ^ 2 ∧
    (Ideal.span ({(⟨1, 1⟩ : GaussianInt)} : Set GaussianInt)).IsPrime := by
  have hi : IsUnit (⟨0, 1⟩ : GaussianInt) :=
    (Zsqrtd.norm_eq_one_iff' (by norm_num) _).mp (by norm_num [Zsqrtd.norm])
  constructor
  · rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
    have he : (⟨1, 1⟩ : GaussianInt) ^ 2 = (2 : GaussianInt) * ⟨0, 1⟩ := by
      ext <;> norm_num [pow_two]
    rw [he, Ideal.span_singleton_mul_right_unit hi]
    simp
  · apply Ideal.isPrime_span_singleton_of_prime
    apply prime_of_prime_norm
    simpa [Zsqrtd.norm] using (Nat.prime_iff_prime_int.mp Nat.prime_two)

/-- A rational prime congruent to 3 modulo 4 generates a prime Gaussian ideal. -/
lemma inert_prime_of_mod_four_eq_three {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ((Ideal.span ({(p : ℤ)} : Set ℤ)).map (Int.castRingHom GaussianInt)).IsPrime := by
  have : Fact p.Prime := ⟨hp⟩
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using
    Ideal.isPrime_span_singleton_of_prime (prime_of_nat_prime_of_mod_four_eq_three p hp4)

/-- Gaussian integers with the same prime norm differ by a unit and possibly conjugation. -/
lemma associated_or_associated_star_of_norm_eq_prime {z w : GaussianInt}
    (hz : Prime z.norm) (hn : w.norm = z.norm) :
    Associated w z ∨ Associated w (star z) := by
  have hpz : Prime z := prime_of_prime_norm hz
  have hpw : Prime w := prime_of_prime_norm (by rwa [hn])
  have hps : Prime (star z) := prime_of_prime_norm (by simpa only [Zsqrtd.norm_conj] using hz)
  have hd : w ∣ z * star z := by
    rw [← Zsqrtd.norm_eq_mul_conj, ← hn, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right w (star w)
  exact (hpw.dvd_or_dvd hd).imp (hpw.associated_of_dvd hpz) (hpw.associated_of_dvd hps)

-- The source's concrete split prime.
example : Ideal.span ({(5 : GaussianInt)} : Set GaussianInt) =
    Ideal.span ({(⟨2, 1⟩ : GaussianInt)} : Set GaussianInt) *
      Ideal.span ({(⟨2, -1⟩ : GaussianInt)} : Set GaussianInt) := by
  rw [Ideal.span_singleton_mul_span_singleton]
  congr 1

-- At the ramified prime, conjugation does not give distinct prime ideals.
example : Associated (⟨1, 1⟩ : GaussianInt) (star (⟨1, 1⟩ : GaussianInt)) := by
  apply associated_of_dvd_dvd
  · exact ⟨⟨0, -1⟩, by ext <;> norm_num⟩
  · exact ⟨⟨0, 1⟩, by ext <;> norm_num⟩

end GaussianInt

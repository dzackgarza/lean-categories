/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.IdealProfiniteCompletion
public import LeanCategories.Algebra.IntegralAdeleRing
public import LeanCategories.ForMathlib.DenseIntegralCompletion
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# The ideal completion of a Dedekind domain

This file compares the inverse limit over all nonzero ideals with the product of the completions
at the height-one primes.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.IdealProfiniteCompletion

open IsDedekindDomain

universe u

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

omit [IsDedekindDomain R] in
theorem quotEquivOfEq_heq {I J : Ideal R} (h : I = J) (x : R ⧸ I) :
    Ideal.quotEquivOfEq h x ≍ x := by
  cases h
  rw [Ideal.quotEquivOfEq_eq_factor, Ideal.Quotient.factor_eq]
  rfl

omit [IsDedekindDomain R] in
theorem evalAdicCompletion_heq_of_place_eq
    {v w : HeightOneSpectrum R} (h : v = w) (n : ℕ)
    (y : (u : HeightOneSpectrum R) → AdicCompletion u.asIdeal R) :
    AdicCompletion.evalₐ v.asIdeal n (y v) ≍
      AdicCompletion.evalₐ w.asIdeal n (y w) := by
  cases h
  rfl

omit [IsDedekindDomain R] in
theorem evalAdicCompletion_heq_of_exponent_eq
    (v : HeightOneSpectrum R) {m n : ℕ} (h : m = n)
    (x : AdicCompletion v.asIdeal R) :
    AdicCompletion.evalₐ v.asIdeal m x ≍ AdicCompletion.evalₐ v.asIdeal n x := by
  cases h
  rfl

/-- A prime power, regarded as a nonzero ideal. -/
def primePower (v : HeightOneSpectrum R) (n : ℕ) : NonzeroIdeal R :=
  ⟨v.asIdeal ^ n, pow_ne_zero n v.ne_bot⟩

theorem eval_primePower_compatible (v : HeightOneSpectrum R) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow v.asIdeal hmn).comp
        (eval R (primePower R v n)).toRingHom =
          (eval R (primePower R v m)).toRingHom := by
  intro m n hmn
  ext x
  exact x.2 (primePower R v n) (primePower R v m)
    (Ideal.pow_le_pow_right hmn)

/-- Restriction of an all-ideal compatible family to the powers of one prime. -/
def toPrimeAdicComponent (v : HeightOneSpectrum R) :
    Completion R →+* AdicCompletion v.asIdeal R :=
  AdicCompletion.liftRingHom v.asIdeal
    (fun n ↦ (eval R (primePower R v n)).toRingHom)
      (eval_primePower_compatible R v)

/-- Restriction to every prime-power subsystem. -/
def toPrimeAdic : Completion R →+*
    ((v : HeightOneSpectrum R) → AdicCompletion v.asIdeal R) :=
  RingHom.pi (toPrimeAdicComponent R)

omit [IsDedekindDomain R] in
theorem factorPow_evalₐ (v : HeightOneSpectrum R) {m n : ℕ} (hmn : m ≤ n)
    (x : AdicCompletion v.asIdeal R) :
    Ideal.Quotient.factorPow v.asIdeal hmn
      (AdicCompletion.evalₐ v.asIdeal n x) =
        AdicCompletion.evalₐ v.asIdeal m x := by
  let hm : (v.asIdeal ^ m • ⊤ : Ideal R) = v.asIdeal ^ m := Ideal.mul_top _
  apply (Ideal.quotientEquivAlgOfEq R hm).symm.injective
  simp only [Ideal.quotientEquivAlgOfEq_symm]
  change Ideal.Quotient.factor (le_of_eq hm.symm)
      (Ideal.Quotient.factorPow v.asIdeal hmn
        (AdicCompletion.evalₐ v.asIdeal n x)) =
    Ideal.Quotient.factor (le_of_eq hm.symm)
      (AdicCompletion.evalₐ v.asIdeal m x)
  rw [AdicCompletion.factor_evalₐ_eq_eval (I := v.asIdeal) (R := R) x
    (le_of_eq hm.symm)]
  change Ideal.Quotient.factor (le_of_eq hm.symm)
      (Ideal.Quotient.factorPow v.asIdeal hmn
        (AdicCompletion.evalₐ v.asIdeal n x)) = x.1 m
  rw [← x.2 hmn]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ v.asIdeal n x)
  have hraw := AdicCompletion.factor_evalₐ_eq_eval
    (I := v.asIdeal) (R := R) x
      (show v.asIdeal ^ n ≤ v.asIdeal ^ n • ⊤ by simp)
  rw [← hr] at hraw ⊢
  change Ideal.Quotient.factor _ (Ideal.Quotient.mk _ r) = x.1 n at hraw
  rw [← hraw]
  simp [AdicCompletion.transitionMap, Ideal.Quotient.factorPow]

@[simp]
theorem eval_toPrimeAdicComponent (v : HeightOneSpectrum R) (n : ℕ)
    (x : Completion R) :
    AdicCompletion.evalₐ v.asIdeal n (toPrimeAdicComponent R v x) =
      eval R (primePower R v n) x := by
  rw [toPrimeAdicComponent, AdicCompletion.evalₐ_liftRingHom]
  rfl

/-- The height-one prime represented by one factor of a nonzero ideal. -/
def factorPlace {I : Ideal R} (P : (UniqueFactorizationMonoid.factors I).toFinset) :
    HeightOneSpectrum R :=
  ⟨P, Ideal.isPrime_of_prime
    (UniqueFactorizationMonoid.prime_of_factor (P : Ideal R)
      (Multiset.mem_toFinset.mp P.prop)),
      (UniqueFactorizationMonoid.prime_of_factor (P : Ideal R)
        (Multiset.mem_toFinset.mp P.prop)).ne_zero⟩

@[simp]
theorem factorPlace_asIdeal {I : Ideal R}
    (P : (UniqueFactorizationMonoid.factors I).toFinset) :
    (factorPlace R P).asIdeal = P := rfl

/-- The exponent of a prime in the factorization of an ideal. -/
def factorExponent {I : Ideal R} (P : (UniqueFactorizationMonoid.factors I).toFinset) : ℕ :=
  Multiset.count (P : Ideal R) (UniqueFactorizationMonoid.factors I)

@[simp]
theorem factorExponent_apply {I : Ideal R}
    (P : (UniqueFactorizationMonoid.factors I).toFinset) :
    factorExponent R P = Multiset.count (P : Ideal R)
      (UniqueFactorizationMonoid.factors I) := rfl

/-- The valuation of an ideal at a height-one prime. -/
def idealExponent (I : Ideal R) (v : HeightOneSpectrum R) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk I).factors

theorem count_factors_eq_idealExponent {I : Ideal R} (hI : I ≠ ⊥)
    (v : HeightOneSpectrum R) :
    Multiset.count v.asIdeal (UniqueFactorizationMonoid.factors I) =
      idealExponent R I v :=
  (congrArg (Multiset.count v.asIdeal)
    (UniqueFactorizationMonoid.factors_eq_normalizedFactors I)).trans <|
      (Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot).symm

theorem factorExponent_eq_idealExponent {I : Ideal R} (hI : I ≠ ⊥)
    (P : (UniqueFactorizationMonoid.factors I).toFinset) :
    factorExponent R P = idealExponent R I (factorPlace R P) := by
  rw [factorExponent, idealExponent]
  simp only [factorPlace_asIdeal]
  exact count_factors_eq_idealExponent R hI (factorPlace R P)

theorem idealExponent_anti {I J : Ideal R} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (h : I ≤ J) (v : HeightOneSpectrum R) :
    idealExponent R J v ≤ idealExponent R I v := by
  apply (Associates.prime_pow_dvd_iff_le
    (Associates.mk_ne_zero.mpr hI) v.associates_irreducible).1
  exact ((Associates.prime_pow_dvd_iff_le
    (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible).2 le_rfl).trans <| by
      rw [Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]
      exact h

/-- A prime factor of `J` is also a prime factor of every nonzero ideal contained in `J`. -/
def factorOfLe {I J : NonzeroIdeal R} (h : (I : Ideal R) ≤ J)
    (P : (UniqueFactorizationMonoid.factors (J : Ideal R)).toFinset) :
    (UniqueFactorizationMonoid.factors (I : Ideal R)).toFinset := by
  refine ⟨P, Multiset.mem_toFinset.mpr (Multiset.count_pos.mp ?_)⟩
  change 0 < Multiset.count (factorPlace R P).asIdeal
    (UniqueFactorizationMonoid.factors (I : Ideal R))
  rw [count_factors_eq_idealExponent R I.prop]
  have hposJ : 0 < idealExponent R J (factorPlace R P) := by
    rw [← factorExponent_eq_idealExponent R J.prop P]
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.prop)
  exact hposJ.trans_le (idealExponent_anti R I.prop J.prop h (factorPlace R P))

@[simp]
theorem factorOfLe_coe {I J : NonzeroIdeal R} (h : (I : Ideal R) ≤ J)
    (P : (UniqueFactorizationMonoid.factors (J : Ideal R)).toFinset) :
    (factorOfLe R h P : Ideal R) = P := rfl

theorem factorExponent_le_factorExponent {I J : NonzeroIdeal R}
    (h : (I : Ideal R) ≤ J)
    (P : (UniqueFactorizationMonoid.factors (J : Ideal R)).toFinset) :
    factorExponent R P ≤ factorExponent R (factorOfLe R h P) := by
  rw [factorExponent_eq_idealExponent R J.prop P,
    factorExponent_eq_idealExponent R I.prop (factorOfLe R h P)]
  exact idealExponent_anti R I.prop J.prop h (factorPlace R P)

theorem ideal_le_factorPower {I : Ideal R} (hI : I ≠ ⊥)
    (P : (UniqueFactorizationMonoid.factors I).toFinset) :
    I ≤ (factorPlace R P).asIdeal ^ factorExponent R P := by
  intro r hr
  have hz : Ideal.Quotient.mk I r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
  have hz' := congrArg
    (fun z ↦ IsDedekindDomain.quotientEquivPiFactors hI z P) hz
  simpa [factorPlace, factorExponent, Ideal.Quotient.eq_zero_iff_mem] using hz'

theorem quotientEquivPiFactors_apply
    {I : Ideal R} (hI : I ≠ ⊥)
    (P : (UniqueFactorizationMonoid.factors I).toFinset)
    (z : R ⧸ I) :
    IsDedekindDomain.quotientEquivPiFactors hI z P =
      Ideal.Quotient.factor (ideal_le_factorPower R hI P) z := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

theorem toPrimeAdic_injective : Function.Injective (toPrimeAdic R) := by
  intro x y hxy
  ext I
  apply (IsDedekindDomain.quotientEquivPiFactors I.prop).injective
  funext P
  rw [quotientEquivPiFactors_apply R I.prop P,
    quotientEquivPiFactors_apply R I.prop P]
  have hx := x.2 I (primePower R (factorPlace R P) (factorExponent R P))
    (ideal_le_factorPower R I.prop P)
  have hy := y.2 I (primePower R (factorPlace R P) (factorExponent R P))
    (ideal_le_factorPower R I.prop P)
  have hcomponent := congrFun hxy (factorPlace R P)
  have hlocal := congrArg
    (AdicCompletion.evalₐ (factorPlace R P).asIdeal (factorExponent R P)) hcomponent
  change AdicCompletion.evalₐ (factorPlace R P).asIdeal (factorExponent R P)
      (toPrimeAdicComponent R (factorPlace R P) x) =
    AdicCompletion.evalₐ (factorPlace R P).asIdeal (factorExponent R P)
      (toPrimeAdicComponent R (factorPlace R P) y) at hlocal
  rw [eval_toPrimeAdicComponent, eval_toPrimeAdicComponent] at hlocal
  convert hx.trans (hlocal.trans hy.symm) using 1 <;>
    simp [transition, primePower, factorPlace, factorExponent] <;> rfl

/-- Evaluation at one prime factor of an ideal. -/
def factorEval (I : NonzeroIdeal R)
    (P : (UniqueFactorizationMonoid.factors (I : Ideal R)).toFinset) :
    ((v : HeightOneSpectrum R) → AdicCompletion v.asIdeal R) →+*
      R ⧸ ((P : Ideal R) ^ Multiset.count (P : Ideal R)
        (UniqueFactorizationMonoid.factors (I : Ideal R))) := by
  let h : (factorPlace R P).asIdeal ^ factorExponent R P =
      (P : Ideal R) ^ Multiset.count (P : Ideal R)
        (UniqueFactorizationMonoid.factors (I : Ideal R)) := by
    rfl
  exact (Ideal.quotEquivOfEq h).toRingHom.comp <|
    (AdicCompletion.evalₐ (factorPlace R P).asIdeal (factorExponent R P)).toRingHom.comp
      (Pi.evalRingHom _ (factorPlace R P))

theorem factorEval_eq_mk (I : NonzeroIdeal R)
    (P : (UniqueFactorizationMonoid.factors (I : Ideal R)).toFinset)
    (y : (v : HeightOneSpectrum R) → AdicCompletion v.asIdeal R) (r : R)
    (h : (↑(AdicCompletion.evalₐ (factorPlace R P).asIdeal
      (factorExponent R P)) : _ → _) (y (factorPlace R P)) =
        Ideal.Quotient.mk _ r) :
    factorEval R I P y = Ideal.Quotient.mk _ r := by
  let e : (factorPlace R P).asIdeal ^ factorExponent R P =
      (P : Ideal R) ^ Multiset.count (P : Ideal R)
        (UniqueFactorizationMonoid.factors (I : Ideal R)) := rfl
  change Ideal.quotEquivOfEq e
      ((↑(AdicCompletion.evalₐ (factorPlace R P).asIdeal
        (factorExponent R P)) : _ → _) (y (factorPlace R P))) = _
  calc
    _ = Ideal.quotEquivOfEq e (Ideal.Quotient.mk _ r) := congrArg _ h
    _ = _ := Ideal.quotEquivOfEq_mk e r

/-- Reconstruct one residue class from its components at the prime factors of the ideal. -/
def fromPrimeAdicResidue (I : NonzeroIdeal R) :
    ((v : HeightOneSpectrum R) → AdicCompletion v.asIdeal R) →+* R ⧸ (I : Ideal R) :=
  (IsDedekindDomain.quotientEquivPiFactors I.prop).symm.toRingHom.comp <|
    RingHom.pi (factorEval R I)

@[simp]
theorem quotientEquivPiFactors_fromPrimeAdicResidue
    (I : NonzeroIdeal R)
    (y : (v : HeightOneSpectrum R) → AdicCompletion v.asIdeal R) :
    IsDedekindDomain.quotientEquivPiFactors I.prop
      (fromPrimeAdicResidue R I y) = fun P ↦ factorEval R I P y := by
  rw [fromPrimeAdicResidue]
  change IsDedekindDomain.quotientEquivPiFactors I.prop
      ((IsDedekindDomain.quotientEquivPiFactors I.prop).symm
        ((RingHom.pi (factorEval R I)) y)) = _
  exact (IsDedekindDomain.quotientEquivPiFactors I.prop).apply_symm_apply _

theorem factor_fromPrimeAdicResidue
    (I : NonzeroIdeal R)
    (P : (UniqueFactorizationMonoid.factors (I : Ideal R)).toFinset)
    (y : (v : HeightOneSpectrum R) → AdicCompletion v.asIdeal R) :
    Ideal.Quotient.factor (ideal_le_factorPower R I.prop P)
      (fromPrimeAdicResidue R I y) = factorEval R I P y := by
  rw [← quotientEquivPiFactors_apply R I.prop P]
  simp

theorem fromPrimeAdicResidue_compatible
    (I J : NonzeroIdeal R) (h : (I : Ideal R) ≤ J) :
    (Ideal.Quotient.factor h).comp (fromPrimeAdicResidue R I) =
      fromPrimeAdicResidue R J := by
  ext y
  apply (IsDedekindDomain.quotientEquivPiFactors J.prop).injective
  funext P
  simp only [RingHom.comp_apply]
  rw [quotientEquivPiFactors_apply R J.prop P,
    quotientEquivPiFactors_fromPrimeAdicResidue]
  rw [Ideal.Quotient.factor_comp_apply]
  let Q := factorOfLe R h P
  let he := factorExponent_le_factorExponent R h P
  have hpowers : (Q : Ideal R) ^ Multiset.count (Q : Ideal R)
        (UniqueFactorizationMonoid.factors (I : Ideal R)) ≤
      (P : Ideal R) ^ Multiset.count (P : Ideal R)
        (UniqueFactorizationMonoid.factors (J : Ideal R)) := by
    exact Ideal.pow_le_pow_right he
  have hplace : factorPlace R Q = factorPlace R P := HeightOneSpectrum.ext rfl
  have hIQ : (I : Ideal R) ≤ (Q : Ideal R) ^ Multiset.count (Q : Ideal R)
      (UniqueFactorizationMonoid.factors (I : Ideal R)) := by
    simpa only [factorPlace_asIdeal, factorExponent_apply] using
      ideal_le_factorPower R I.prop Q
  calc
    Ideal.Quotient.factor _ (fromPrimeAdicResidue R I y) =
        Ideal.Quotient.factor hpowers
          (Ideal.Quotient.factor hIQ
            (fromPrimeAdicResidue R I y)) := by
      rw [Ideal.Quotient.factor_comp_apply]
    _ = Ideal.Quotient.factor hpowers (factorEval R I Q y) := by
      congr 1
      exact factor_fromPrimeAdicResidue R I Q y
    _ = factorEval R J P y := by
      have hy : HEq (y (factorPlace R Q)) (y (factorPlace R P)) := by
        rw [hplace]
      have hlocal := factorPow_evalₐ R (factorPlace R Q) he
        (y (factorPlace R Q))
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ (factorPlace R Q).asIdeal
          (factorExponent R Q) (y (factorPlace R Q)))
      rw [← hr] at hlocal
      have hQ := factorEval_eq_mk R I Q y r hr.symm
      have hlocal' : AdicCompletion.evalₐ (factorPlace R Q).asIdeal
          (factorExponent R P) (y (factorPlace R Q)) =
            Ideal.Quotient.mk _ r := by
        rw [← hlocal]
        rfl
      have hP : AdicCompletion.evalₐ (factorPlace R P).asIdeal
          (factorExponent R P) (y (factorPlace R P)) =
            Ideal.Quotient.mk _ r := by
        cases hy
        exact hlocal'
      have hJ := factorEval_eq_mk R J P y r hP
      rw [hQ, hJ]
      rfl

/-- A family of prime-adic elements determines one compatible residue class modulo every
nonzero ideal. -/
def fromPrimeAdic :
    ((v : HeightOneSpectrum R) → AdicCompletion v.asIdeal R) →+* Completion R where
  toFun y := ⟨fun I ↦ fromPrimeAdicResidue R I y, fun I J h ↦
    RingHom.congr_fun (fromPrimeAdicResidue_compatible R I J h) y⟩
  map_one' := by
    apply Subtype.ext
    funext I
    exact map_one (fromPrimeAdicResidue R I)
  map_mul' x y := by
    apply Subtype.ext
    funext I
    exact map_mul (fromPrimeAdicResidue R I) x y
  map_zero' := by
    apply Subtype.ext
    funext I
    exact map_zero (fromPrimeAdicResidue R I)
  map_add' x y := by
    apply Subtype.ext
    funext I
    exact map_add (fromPrimeAdicResidue R I) x y

theorem eval_fromPrimeAdic (I : NonzeroIdeal R)
    (y : (v : HeightOneSpectrum R) → AdicCompletion v.asIdeal R) :
    eval R I (fromPrimeAdic R y) = fromPrimeAdicResidue R I y := rfl

theorem fromPrimeAdic_toPrimeAdic (x : Completion R) :
    fromPrimeAdic R (toPrimeAdic R x) = x := by
  ext I
  apply (IsDedekindDomain.quotientEquivPiFactors I.prop).injective
  funext P
  change IsDedekindDomain.quotientEquivPiFactors I.prop
      (fromPrimeAdicResidue R I (toPrimeAdic R x)) P =
    IsDedekindDomain.quotientEquivPiFactors I.prop (eval R I x) P
  rw [quotientEquivPiFactors_apply R I.prop P,
    quotientEquivPiFactors_apply R I.prop P,
    factor_fromPrimeAdicResidue R I P]
  have hx := x.2 I
    (primePower R (factorPlace R P) (factorExponent R P))
      (ideal_le_factorPower R I.prop P)
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    (eval R (primePower R (factorPlace R P) (factorExponent R P)) x)
  have heval : AdicCompletion.evalₐ (factorPlace R P).asIdeal
      (factorExponent R P)
        (toPrimeAdic R x (factorPlace R P)) = Ideal.Quotient.mk _ r := by
    change AdicCompletion.evalₐ (factorPlace R P).asIdeal
      (factorExponent R P)
        (toPrimeAdicComponent R (factorPlace R P) x) = _
    rw [eval_toPrimeAdicComponent]
    exact hr.symm
  have hfactor := factorEval_eq_mk R I P (toPrimeAdic R x) r heval
  rw [hfactor]
  change Ideal.Quotient.factor _ (eval R I x) =
      eval R (primePower R (factorPlace R P) (factorExponent R P)) x at hx
  exact hr.trans hx.symm

theorem factors_primePower (v : HeightOneSpectrum R) (n : ℕ) :
    UniqueFactorizationMonoid.factors (v.asIdeal ^ n) =
      Multiset.replicate n v.asIdeal := by
  rw [UniqueFactorizationMonoid.factors_eq_normalizedFactors,
    v.irreducible.normalizedFactors_pow]
  simp

/-- The unique prime factor of a positive power of a height-one prime. -/
def primePowerFactor (v : HeightOneSpectrum R) (n : ℕ) :
    (UniqueFactorizationMonoid.factors (v.asIdeal ^ (n + 1))).toFinset := by
  refine ⟨v.asIdeal, Multiset.mem_toFinset.mpr ?_⟩
  rw [factors_primePower]
  simp

@[simp]
theorem factorPlace_primePowerFactor (v : HeightOneSpectrum R) (n : ℕ) :
    factorPlace R (primePowerFactor R v n) = v := by
  apply HeightOneSpectrum.ext
  rfl

theorem factorExponent_primePowerFactor (v : HeightOneSpectrum R) (n : ℕ) :
    factorExponent R (primePowerFactor R v n) = n + 1 := by
  change Multiset.count v.asIdeal
    (UniqueFactorizationMonoid.factors (v.asIdeal ^ (n + 1))) = n + 1
  rw [factors_primePower]
  simp

set_option maxHeartbeats 1000000 in
-- Dependent transport across height-one places is expensive for the elaborator.
theorem eval_fromPrimeAdic_primePower (v : HeightOneSpectrum R) (n : ℕ)
    (y : (w : HeightOneSpectrum R) → AdicCompletion w.asIdeal R) :
    eval R (primePower R v n) (fromPrimeAdic R y) =
      AdicCompletion.evalₐ v.asIdeal n (y v) := by
  cases n with
  | zero =>
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
        (eval R (primePower R v 0) (fromPrimeAdic R y))
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ v.asIdeal 0 (y v))
      rw [← ha, ← hb]
      apply Ideal.Quotient.eq.mpr
      simp [primePower]
  | succ n =>
      let P := primePowerFactor R v n
      have hf := factor_fromPrimeAdicResidue R (primePower R v (n + 1)) P y
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
        (fromPrimeAdicResidue R (primePower R v (n + 1)) y)
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ (factorPlace R P).asIdeal
          (factorExponent R P) (y (factorPlace R P)))
      rw [← hr] at hf
      simp only [Ideal.Quotient.factor_mk] at hf
      have hfactor := factorEval_eq_mk R (primePower R v (n + 1)) P y s hs.symm
      rw [hfactor] at hf
      have htarget : (factorPlace R P).asIdeal ^ factorExponent R P =
          v.asIdeal ^ (n + 1) := by
        have hp : factorPlace R P = v := by
          dsimp [P]
          exact factorPlace_primePowerFactor R v n
        have he : factorExponent R P = n + 1 := by
          dsimp [P]
          exact factorExponent_primePowerFactor R v n
        rw [hp, he]
      have hmem : r - s ∈ (factorPlace R P).asIdeal ^ factorExponent R P :=
        Ideal.Quotient.eq.mp hf
      have hmk : Ideal.Quotient.mk (v.asIdeal ^ (n + 1)) r =
          Ideal.Quotient.mk (v.asIdeal ^ (n + 1)) s := by
        apply Ideal.Quotient.eq.mpr
        rwa [← htarget]
      have hp : factorPlace R P = v := by
        dsimp [P]
        exact factorPlace_primePowerFactor R v n
      have he : factorExponent R P = n + 1 := by
        dsimp [P]
        exact factorExponent_primePowerFactor R v n
      have heval : Ideal.quotEquivOfEq htarget
          (AdicCompletion.evalₐ (factorPlace R P).asIdeal
            (factorExponent R P) (y (factorPlace R P))) =
          AdicCompletion.evalₐ v.asIdeal (n + 1) (y v) := by
        have hv := evalAdicCompletion_heq_of_place_eq R hp (factorExponent R P) y
        have hn := evalAdicCompletion_heq_of_exponent_eq R v he (y v)
        exact eq_of_heq ((quotEquivOfEq_heq R htarget _).trans (hv.trans hn))
      have hs' : Ideal.Quotient.mk (v.asIdeal ^ (n + 1)) s =
          AdicCompletion.evalₐ v.asIdeal (n + 1) (y v) := by
        simpa only [Ideal.quotEquivOfEq_mk] using
          (congrArg (Ideal.quotEquivOfEq htarget) hs).trans heval
      rw [eval_fromPrimeAdic, ← hr]
      exact hmk.trans hs'

theorem toPrimeAdic_fromPrimeAdic
    (y : (v : HeightOneSpectrum R) → AdicCompletion v.asIdeal R) :
    toPrimeAdic R (fromPrimeAdic R y) = y := by
  funext v
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ v.asIdeal n
      (toPrimeAdicComponent R v (fromPrimeAdic R y)) = _
  rw [eval_toPrimeAdicComponent, eval_fromPrimeAdic_primePower]

/-- The inverse limit over all nonzero ideals of a Dedekind domain is the product of its
prime-adic completions. -/
def completionEquivPrimeAdic : Completion R ≃+*
    ((v : HeightOneSpectrum R) → AdicCompletion v.asIdeal R) where
  toFun := toPrimeAdic R
  invFun := fromPrimeAdic R
  left_inv := fromPrimeAdic_toPrimeAdic R
  right_inv := toPrimeAdic_fromPrimeAdic R
  map_add' := map_add (toPrimeAdic R)
  map_mul' := map_mul (toPrimeAdic R)

variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The inverse limit of all nonzero ideal quotients is the integral finite adele ring. -/
def completionEquivFiniteIntegralAdele :
    Completion R ≃+* FiniteIntegralAdeleRing R K :=
  (completionEquivPrimeAdic R).trans <|
    RingEquiv.piCongrRight fun v ↦
      IsDedekindDomain.HeightOneSpectrum.adicCompletionEquivAdicCompletionIntegers K v

end LeanCategories.IdealProfiniteCompletion

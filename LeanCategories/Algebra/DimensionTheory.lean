/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Dimension theory

This file owns the project-specific system-of-parameters, Hilbert-series, and
prime-presented affine-variety dimension definitions. Other dimension notions
remain the canonical Mathlib declarations.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u v

open Filter Polynomial
open scoped LaurentSeries

section LocalRings

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- A finite sequence is a system of parameters when it generates an ideal
whose radical is the maximal ideal. -/
def IsSystemOfParameters {n : ℕ} (x : Fin n → R) : Prop :=
  (Ideal.span (Set.range x)).radical = IsLocalRing.maximalIdeal R

end LocalRings

section DeltaInvariant

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Numbers of generators of maximal-primary ideals. A family belongs to this
set exactly when the radical of the ideal it generates is the maximal ideal. -/
def DeltaGeneratorCounts : Set ℕ :=
  {n : ℕ | ∃ x : Fin n → R,
    (Ideal.span (Set.range x)).radical = IsLocalRing.maximalIdeal R}

/-- The set of generator counts defining `DeltaInvariant` is nonempty in a
Noetherian local ring. -/
theorem deltaGeneratorCounts_nonempty [IsNoetherianRing R] : (DeltaGeneratorCounts R).Nonempty := by
  obtain ⟨S, hSfin, hspan⟩ := Submodule.fg_def.mp
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R))
  let e : S ≃ Fin (@Fintype.card S hSfin.fintype) :=
    @Fintype.equivFin S hSfin.fintype
  let x : Fin (@Fintype.card S hSfin.fintype) → R := fun i => (e.symm i).1
  refine ⟨@Fintype.card S hSfin.fintype, x, ?_⟩
  have hrange : Set.range x = S := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hr
      refine ⟨e ⟨r, hr⟩, ?_⟩
      exact congrArg Subtype.val (e.symm_apply_apply ⟨r, hr⟩)
  rw [hrange]
  have hspan' : Ideal.span S = IsLocalRing.maximalIdeal R := by
    ext r
    change r ∈ Submodule.span R S ↔ r ∈ IsLocalRing.maximalIdeal R
    rw [hspan]
  rw [hspan']
  exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical

/-- Atiyah--Macdonald's `δ(A)`: the least number of generators of an
`m`-primary ideal in a Noetherian local ring. -/
noncomputable def DeltaInvariant : ℕ :=
  sInf (DeltaGeneratorCounts R)

/-- `DeltaInvariant` is itself attained by a maximal-primary generating family. -/
theorem deltaInvariant_mem [IsNoetherianRing R] : DeltaInvariant R ∈ DeltaGeneratorCounts R :=
  Nat.sInf_mem (deltaGeneratorCounts_nonempty R)

/-- `DeltaInvariant` is no larger than any other maximal-primary generator count. -/
theorem deltaInvariant_le {n : ℕ} (hn : n ∈ DeltaGeneratorCounts R) : DeltaInvariant R ≤ n :=
  Nat.sInf_le hn

end DeltaInvariant

section PrimeDepth

variable {R : Type u} [CommRing R]

/-- Atiyah--Macdonald's chain-theoretic depth of a prime ideal: the supremum
of lengths of chains of prime ideals beginning at `p`. This is unrelated to the
modern homological notion also called depth. -/
noncomputable def PrimeIdealDepth (p : PrimeSpectrum R) : ℕ∞ :=
  Order.coheight p

/-- The source comparison `depth p = dim (R/p)`. -/
theorem primeIdealDepth_eq_ringKrullDim_quotient (p : PrimeSpectrum R) :
    (PrimeIdealDepth p : WithBot ℕ∞) = ringKrullDim (R ⧸ p.asIdeal) := by
  rw [ringKrullDim_quotient, PrimeIdealDepth, Order.coheight_eq_krullDim_Ici]
  apply Order.krullDim_eq_of_orderIso
  apply OrderIso.setCongr
  ext q
  simp [PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.asIdeal_le_asIdeal]

end PrimeDepth

section Hilbert

variable {R : Type u} [Semiring R]
variable (lambda : ∀ {N : Type v} [AddCommMonoid N] [Module R N], ℤ)
variable (M : ℕ → Type v) [∀ n, AddCommMonoid (M n)] [∀ n, Module R (M n)]

/-- The Hilbert function of a graded module, relative to an additive invariant. -/
def HilbertFunction : ℕ → ℤ :=
  fun n => @lambda (M n) (inferInstance : AddCommMonoid (M n))
    (inferInstance : Module R (M n))

/-- The Poincare series of a graded module. -/
def PoincareSeries : PowerSeries ℤ :=
  PowerSeries.mk (R := ℤ) (fun n => @lambda (M n) (inferInstance : AddCommMonoid (M n))
    (inferInstance : Module R (M n)))

end Hilbert

section EventualPolynomial

/-- A rational polynomial that agrees eventually with an integer-valued sequence. -/
def IsEventuallyPolynomial (f : ℕ → ℤ) (p : ℚ[X]) : Prop :=
  ∀ᶠ n in atTop, (f n : ℚ) = p.eval (n : ℚ)

/-- An eventual polynomial is unique. -/
theorem IsEventuallyPolynomial.unique {f : ℕ → ℤ} {p q : ℚ[X]}
    (hp : IsEventuallyPolynomial f p) (hq : IsEventuallyPolynomial f q) : p = q := by
  rw [IsEventuallyPolynomial, Filter.eventually_atTop] at hp hq
  obtain ⟨Np, hp⟩ := hp
  obtain ⟨Nq, hq⟩ := hq
  let N := max Np Nq
  apply Polynomial.eq_of_infinite_eval_eq p q
  refine (Set.infinite_range_of_injective (f := fun k : ℕ => ((N + k : ℕ) : ℚ)) ?_).mono ?_
  · intro a b hab
    exact Nat.add_left_cancel (Nat.cast_injective hab)
  · rintro x ⟨k, rfl⟩
    change p.eval ((N + k : ℕ) : ℚ) = q.eval ((N + k : ℕ) : ℚ)
    exact (hp (N + k) (le_trans (le_max_left _ _) (Nat.le_add_right _ _))).symm.trans
      (hq (N + k) (le_trans (le_max_right _ _) (Nat.le_add_right _ _)))

/-- The unique eventual polynomial, given its existence. This is the generic
owner used for Atiyah--Macdonald's Hilbert and Hilbert--Samuel polynomials. -/
noncomputable def eventualPolynomial (f : ℕ → ℤ)
    (h : ∃ p : ℚ[X], IsEventuallyPolynomial f p) : ℚ[X] :=
  Classical.choose h

theorem eventualPolynomial_spec (f : ℕ → ℤ)
    (h : ∃ p : ℚ[X], IsEventuallyPolynomial f p) :
    IsEventuallyPolynomial f (eventualPolynomial f h) :=
  Classical.choose_spec h

end EventualPolynomial

section PoincarePoleOrder

/-- The canonical embedding of rational functions into Laurent series at zero.
It is written explicitly because Mathlib's coercion uses a non-exported local
`Algebra` instance. -/
noncomputable def ratFuncToLaurentSeries : RatFunc ℚ →+* LaurentSeries ℚ := by
  let φ : ℚ[X] →+* LaurentSeries ℚ := algebraMap _ _
  have hφ : Function.Injective φ :=
    FaithfulSMul.algebraMap_injective ℚ[X] (LaurentSeries ℚ)
  exact RatFunc.liftRingHom φ
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφ)

theorem ratFuncToLaurentSeries_injective : Function.Injective ratFuncToLaurentSeries := by
  let φ : ℚ[X] →+* LaurentSeries ℚ := algebraMap _ _
  have hφ : Function.Injective φ :=
    FaithfulSMul.algebraMap_injective ℚ[X] (LaurentSeries ℚ)
  exact RatFunc.liftRingHom_injective φ hφ

/-- A rational function whose Laurent expansion at zero is the rationalization
of the integral power series `P`. -/
def RepresentsPowerSeries (P : PowerSeries ℤ) (r : RatFunc ℚ) : Prop :=
  (((P.map (Int.castRingHom ℚ)) : PowerSeries ℚ) : LaurentSeries ℚ) =
    ratFuncToLaurentSeries r

theorem RepresentsPowerSeries.unique {P : PowerSeries ℤ} {r s : RatFunc ℚ}
    (hr : RepresentsPowerSeries P r) (hs : RepresentsPowerSeries P s) : r = s := by
  apply ratFuncToLaurentSeries_injective
  exact hr.symm.trans hs

/-- The pole order at `t = 1` of a reduced rational function. Since `RatFunc.denom`
is the canonical denominator coprime to the numerator, this is exactly the
multiplicity of `1` as a root of the denominator. -/
noncomputable def RationalPoleOrderAtOne (r : RatFunc ℚ) : ℕ :=
  r.denom.rootMultiplicity 1

/-- The pole order at `t = 1` of a rational integral power series, given the
rationality witness. Applied to `PoincareSeries`, this is Atiyah--Macdonald's `d(M)`. -/
noncomputable def PowerSeriesPoleOrderAtOne (P : PowerSeries ℤ)
    (h : ∃ r : RatFunc ℚ, RepresentsPowerSeries P r) : ℕ :=
  RationalPoleOrderAtOne (Classical.choose h)

end PoincarePoleOrder

section HilbertSamuel

variable {R : Type u} [CommRing R]
variable (q : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The integer-valued Hilbert--Samuel length sequence. In Atiyah--Macdonald's
source context Proposition 11.4(i) supplies finiteness of these lengths. -/
noncomputable def HilbertSamuelFunction (n : ℕ) : ℤ :=
  ((Module.length R (M ⧸ (q ^ n • ⊤ : Submodule R M))).toNat : ℤ)

/-- Atiyah--Macdonald's characteristic polynomial `χ_q^M`, given the eventual
polynomiality supplied by Proposition 11.4. -/
noncomputable def CharacteristicPolynomial
    (h : ∃ p : ℚ[X], IsEventuallyPolynomial (HilbertSamuelFunction q M) p) : ℚ[X] :=
  eventualPolynomial (HilbertSamuelFunction q M) h

end HilbertSamuel

section LocalHilbertSamuel

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Atiyah--Macdonald's local invariant `d(A)`, defined using the degree of the
characteristic polynomial for the maximal ideal. Proposition 11.6 later proves
that every maximal-primary characteristic polynomial has the same degree. -/
noncomputable def LocalHilbertSamuelDimension
    (h : ∃ p : ℚ[X], IsEventuallyPolynomial
      (HilbertSamuelFunction (IsLocalRing.maximalIdeal R) R) p) : ℕ :=
  (CharacteristicPolynomial (IsLocalRing.maximalIdeal R) R h).natDegree

end LocalHilbertSamuel

section AffineVarieties

variable {k : Type u} [Field k]
variable {σ : Type v}

/-- The dimension of a prime-presented affine variety.

This is the transcendence degree of its rational function field over `k`.
-/noncomputable def AffineVarietyDimension
    (P : PrimeSpectrum (MvPolynomial σ k)) : Cardinal.{max u v} := by
  letI : P.1.IsPrime := P.2
  let A := MvPolynomial σ k ⧸ P.1
  letI : Algebra k (FractionRing A) :=
    RingHom.toAlgebra ((algebraMap A (FractionRing A)).comp (algebraMap k A))
  exact Algebra.trdeg k (FractionRing A)

end AffineVarieties

end LeanCategories.Algebra

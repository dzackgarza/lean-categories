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
public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import LeanCategories.Algebra.DummitFooteChapter15

/-!
# Atiyah--Macdonald, Chapter 11: dimension theory

This module gives the standard catalogue names for the dimension-theoretic
objects already owned by Mathlib. It does not introduce a second dimension
theory.

The prime-spectrum order and its `LTSeries` chains are Mathlib's exact
representation of chains of prime ideals. `Ideal.height`, `ringKrullDim`,
`Module.supportDim`, `Order.coheight`, `Algebra.trdeg`, and
`IsRegularLocalRing` are therefore exposed without new definitions.

The terminology for codimension follows Mathlib's algebraic-cycle route:
`Order.coheight` is the standard codimension weight on a spectral space.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u v

section PrimeSpectrum

variable (R : Type u) [CommSemiring R]

/-- A strict chain of prime ideals of `R`. -/
abbrev PrimeIdealChain : Type u := Order.LTSeries (PrimeSpectrum R)

/-- The order height of a prime ideal, represented as a point of `Spec R`. -/
abbrev PrimeIdealHeight : PrimeSpectrum R → ℕ∞ := Order.height

/-- The codimension weight of a prime of `R`. -/
abbrev PrimeIdealCodimension : PrimeSpectrum R → ℕ∞ := Order.coheight

/-- The Krull dimension of the prime spectrum of `R`. -/
abbrev RingKrullDimension : WithBot ℕ∞ := ringKrullDim R

end PrimeSpectrum

section Ideals

variable {R : Type u} [CommRing R]

/-- The height of an ideal, including the prime-ideal case. -/
abbrev IdealHeight (I : Ideal R) : ℕ∞ := I.height

/-- The height of a prime ideal, using Mathlib's ideal representation. -/
abbrev IdealPrimeHeight (P : Ideal R) [P.IsPrime] : ℕ∞ := P.height

end Ideals

section Modules

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The Krull dimension of an `R`-module, defined by its support. -/
abbrev ModuleKrullDimension : WithBot ℕ∞ := Module.supportDim R M

end Modules

section LocalRings

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- A finite sequence is a system of parameters when it generates an ideal
whose radical is the maximal ideal.

This is the standard local-ring definition in Atiyah--Macdonald, Chapter 11,
"Dimension theory of Noetherian local rings", p. 122. -/
def IsSystemOfParameters (x : Fin n → R) : Prop :=
  (Ideal.span (Set.range x)).radical = IsLocalRing.maximalIdeal R

end LocalRings

section Hilbert

variable {R : Type u} [Semiring R]
variable (lambda : ∀ {N : Type v} [AddCommMonoid N] [Module R N], ℤ)
variable (M : ℕ → Type v) [∀ n, AddCommMonoid (M n)] [∀ n, Module R (M n)]

/-- The Hilbert function of a graded module, relative to an additive invariant
on the degree-zero module category.

This is the function `n ↦ lambda (M n)` in Atiyah--Macdonald, Chapter 11,
``Hilbert functions'', p. 118. The finite-generation and additivity
hypotheses belong to the supplied graded module and invariant. -/
def HilbertFunction : ℕ → ℤ :=
  fun n => @lambda (M n) (inferInstance : AddCommMonoid (M n))
    (inferInstance : Module R (M n))

/-- The Poincare series of a graded module.

This is the formal power series `Σ n, lambda (M n) t^n` from
Atiyah--Macdonald, Chapter 11, ``Hilbert functions'', p. 116. It uses
Mathlib's `PowerSeries.mk`; no Hilbert--Serre theorem is asserted here. -/
def PoincareSeries : PowerSeries ℤ :=
  PowerSeries.mk (HilbertFunction lambda M)

/** The Hilbert polynomial route supplied by Mathlib. */
abbrev HilbertPolynomial (F : Type u) [Field F] (p : Polynomial F) (d : ℕ) : Polynomial F :=
  Polynomial.hilbertPoly p d

end Hilbert

section AffineVarieties

open LeanCategories.Algebra.DummitFoote.Chapter15

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {σ : Type v}

/-- The field of rational functions of a prime-presented affine variety.

For `P : Ideal (MvPolynomial σ k)` prime, this is the fraction field of the
coordinate ring `k[X]/P`, as in Atiyah--Macdonald, Chapter 11,
``Transcendental dimension'', p. 124. -/
noncomputable abbrev AffineVarietyFunctionField
    (P : AffineVarietyPrimeIdeal (k := k) (K := K)) : Type u :=
  FractionRing (varietyCoordinateRing P)

/-- The dimension of a prime-presented affine variety.

This is the transcendence degree of its rational function field over `k`.
The fraction-field and transcendence-degree constructions are Mathlib's
`FractionRing` and `Algebra.trdeg`; no dimension comparison theorem is added. -/
noncomputable def AffineVarietyDimension
    (P : AffineVarietyPrimeIdeal (k := k) (K := K)) : Cardinal.{u} := by
  letI : P.1.IsPrime := P.2
  let A := varietyCoordinateRing P
  letI : Algebra k (FractionRing A) :=
    RingHom.toAlgebra ((algebraMap A (FractionRing A)).comp (algebraMap k A))
  exact Algebra.trdeg k (FractionRing A)

/-- The local dimension of a prime-presented affine variety at a maximal
ideal of its coordinate ring.

This is the Krull dimension of the corresponding local ring, represented by
Mathlib's `Localization.AtPrime` and `ringKrullDim`. -/
noncomputable abbrev AffineVarietyLocalDimension
    (P : AffineVarietyPrimeIdeal (k := k) (K := K))
    (m : Ideal (varietyCoordinateRing P)) [m.IsMaximal] : WithBot ℕ∞ :=
  ringKrullDim (Localization.AtPrime m)

end AffineVarieties

section Schemes

open AlgebraicGeometry

variable (X : Scheme.{u})

/** The function field of an irreducible scheme. */
noncomputable abbrev SchemeFunctionField [IrreducibleSpace X] : CommRingCat.{u} :=
  X.functionField

/** The local dimension of a scheme at a point, via its stalk dimension. */
abbrev SchemeLocalDimension (x : X) : ℕ∞ := Order.coheight x

end Schemes

section Transcendence

variable (R : Type u) (A : Type v)
variable [CommRing R] [CommRing A] [Algebra R A]

/-- The transcendence degree of the commutative `R`-algebra `A`. -/
abbrev TranscendenceDegree : Cardinal.{v} := Algebra.trdeg R A

end Transcendence

section RegularLocal

variable (R : Type u) [CommRing R]

/-- A Noetherian local ring whose maximal ideal has dimension-many generators. -/
abbrev RegularLocalRing : Prop := IsRegularLocalRing R

end RegularLocal

end LeanCategories.Algebra

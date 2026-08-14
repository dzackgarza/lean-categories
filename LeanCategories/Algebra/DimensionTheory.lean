/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.RegularLocalRing.Defs

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

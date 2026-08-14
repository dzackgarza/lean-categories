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

/-!
# Dimension theory

This file owns the project-specific system-of-parameters, Hilbert-series, and
prime-presented affine-variety dimension definitions. Other dimension notions
remain the canonical Mathlib declarations.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u v

section LocalRings

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- A finite sequence is a system of parameters when it generates an ideal
whose radical is the maximal ideal. -/
def IsSystemOfParameters {n : ℕ} (x : Fin n → R) : Prop :=
  (Ideal.span (Set.range x)).radical = IsLocalRing.maximalIdeal R

end LocalRings

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
  PowerSeries.mk (HilbertFunction lambda M)

end Hilbert

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

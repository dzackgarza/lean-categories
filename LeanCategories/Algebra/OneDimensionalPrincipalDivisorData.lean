/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# Principal-divisor data for one-dimensional Noetherian domains

Definition-level realization of Neukirch FC09-C01-U115.

For the standing one-dimensional Noetherian domain `A`, Neukirch assigns to
each maximal ideal `p` the local length order `ord_p`, then defines

`div(f) = Σ_p ord_p(f) p`.

Mathlib's `Scheme.ord` on `Spec A` is the native local-length order: its
codimension-one branch is built from `Ring.ordFrac`.  This file records the
coefficient function and constructs the subtype of finitely supported divisors
having exactly those coefficients.  Finiteness of the support, uniqueness,
multiplicativity/additivity, and independence under transport to another
fraction-field model are result-layer statements.

Before subgroup closure is proved, principal divisors are represented by their
literal set-theoretic carrier, so no unwitnessed `AddSubgroup` is selected.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace LeanCategories.Algebra

universe u

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

/-- Neukirch's local order coefficient at a maximal ideal, using the canonical
function field of `Spec A`.

Under the source's standing one-dimensional hypothesis every nonzero maximal
point is codimension one, where `Scheme.ord` is exactly the local-length
fraction-field order `Ring.ordFrac`.  Establishing that comparison is result
content. -/
def localOrderCoefficientData
    (p : MaximalSpectrum A) (f : (Spec (.of A)).functionFieldˣ) : ℤ :=
  (Spec (.of A)).ord
    (f : (Spec (.of A)).functionField)
    p.toPrimeSpectrum

/-- Intrinsic coefficient characterization of Neukirch's principal divisor
`div(f)` in FC09-C01-U115. -/
def IsPrincipalDivisorData
    (f : (Spec (.of A)).functionFieldˣ)
    (D : MaximalSpectrum A →₀ ℤ) : Prop :=
  ∀ p : MaximalSpectrum A, D p = localOrderCoefficientData p f

/-- The carrier of all finitely supported divisors with Neukirch's exact
coefficient formula for `f`.  No divisor is selected before finite support is
proved. -/
def PrincipalDivisorData
    (f : (Spec (.of A)).functionFieldˣ) :=
  {D : MaximalSpectrum A →₀ ℤ // IsPrincipalDivisorData f D}

/-- A divisor is principal when it is selected from a nonzero element of the
function field. -/
def IsPrincipalData (D : MaximalSpectrum A →₀ ℤ) : Prop :=
  ∃ f : (Spec (.of A)).functionFieldˣ, IsPrincipalDivisorData f D

/-- The set-theoretic carrier of principal divisors.  The later homomorphism
theorem supplies the additive-subgroup structure. -/
def principalDivisorCarrierData : Set (MaximalSpectrum A →₀ ℤ) :=
  {D | IsPrincipalData D}

/-- Neukirch's rational equivalence relation: two divisors differ by a
principal divisor. -/
def RationallyEquivalentData
    (D E : MaximalSpectrum A →₀ ℤ) : Prop :=
  D - E ∈ principalDivisorCarrierData (A := A)

end LeanCategories.Algebra

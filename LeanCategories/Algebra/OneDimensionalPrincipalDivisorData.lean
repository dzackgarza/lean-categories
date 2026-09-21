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
coefficient function and selects the finitely supported divisor characterized
by those coefficients.  Finiteness of the support, the specification theorem
for that selection, multiplicativity/additivity, and independence under
transport to another fraction-field model are result-layer statements.

The principal-divisor subgroup is likewise selected by its intrinsic carrier,
so Sweep III does not require the subgroup-closure proof supplied by the later
homomorphism theorem.
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

/-- Neukirch's principal divisor `div(f)`, selected by its coefficient
characterization.

The later finite-support theorem proves that this selection satisfies
`IsPrincipalDivisorData f`; Sweep III records only the construction. -/
def principalDivisorData
    (f : (Spec (.of A)).functionFieldˣ) : MaximalSpectrum A →₀ ℤ :=
  Classical.epsilon (IsPrincipalDivisorData f)

/-- The raw principal-divisor function `f ↦ div(f)`.

The assertion that this is a group homomorphism is result content. -/
def principalDivisorMapData :
    (Spec (.of A)).functionFieldˣ → (MaximalSpectrum A →₀ ℤ) :=
  principalDivisorData

/-- A divisor is principal when it is selected from a nonzero element of the
function field. -/
def IsPrincipalData (D : MaximalSpectrum A →₀ ℤ) : Prop :=
  ∃ f : (Spec (.of A)).functionFieldˣ, D = principalDivisorData f

/-- Predicate characterizing the subgroup of principal divisors. -/
def IsPrincipalDivisorSubgroupData
    (P : AddSubgroup (MaximalSpectrum A →₀ ℤ)) : Prop :=
  ∀ D : MaximalSpectrum A →₀ ℤ, D ∈ P ↔ IsPrincipalData D

/-- Neukirch's subgroup `P(A) ⊆ Div(A)` of principal divisors, selected by
its intrinsic carrier.

Closure follows later from the principal-divisor homomorphism theorem. -/
def principalDivisorSubgroupData : AddSubgroup (MaximalSpectrum A →₀ ℤ) :=
  Classical.epsilon (IsPrincipalDivisorSubgroupData (A := A))

/-- Neukirch's rational equivalence relation: two divisors differ by a
principal divisor. -/
def RationallyEquivalentData
    (D E : MaximalSpectrum A →₀ ℤ) : Prop :=
  D - E ∈ principalDivisorSubgroupData (A := A)

end LeanCategories.Algebra

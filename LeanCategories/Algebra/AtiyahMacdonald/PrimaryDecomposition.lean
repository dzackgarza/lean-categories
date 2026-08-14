/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Lasker

/-!
# Atiyah--Macdonald Chapter 4: primary decomposition

This module routes the Chapter 4 vocabulary to Mathlib's ideal and submodule
definitions. It does not prove primary-decomposition existence or uniqueness.

The primary-decomposition predicates and the isolated/embedded terminology
follow Atiyah--Macdonald, *Introduction to Commutative Algebra*, Chapter 4,
pp. 50--52. The implementation uses Mathlib's `Submodule.IsPrimary`,
`Submodule.IsMinimalPrimaryDecomposition`, and associated-prime definitions.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

/-! ### Primary ideals and decompositions -/

/** A primary ideal, routed to Mathlib's `Ideal.IsPrimary`. */
abbrev primary (I : Ideal R) : Prop := I.IsPrimary

/** A primary submodule, routed to Mathlib's `Submodule.IsPrimary`. */
abbrev primarySubmodule {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) : Prop := N.IsPrimary

/**
An arbitrary finite primary decomposition of an ideal.

This is the Chapter 4 definition `I = ⋂ qᵢ` with every `qᵢ` primary.
Mathlib stores the minimal form as `Submodule.IsMinimalPrimaryDecomposition`.
*/
def IsPrimaryDecomposition (I : Ideal R) (s : Finset (Ideal R)) : Prop :=
  s.inf id = I ∧ ∀ ⦃J : Ideal R⦄, J ∈ s → J.IsPrimary

/** A minimal primary decomposition, using Mathlib's canonical structure. */
abbrev minimalPrimaryDecomposition (I : Ideal R) (s : Finset (Ideal R)) : Prop :=
  Submodule.IsMinimalPrimaryDecomposition I s

/** The Lasker-module property for the regular module `R`. */
abbrev isLaskerRing : Prop := IsLasker R R

/-! ### Primes attached to a primary decomposition -/

/**
The prime candidates attached to a primary decomposition.

For a primary component `q`, its radical is prime. For a minimal primary
decomposition, Mathlib proves that this image is the associated-prime set.
See `Submodule.IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes`.
*/
def primaryDecompositionPrimes (I : Ideal R) (s : Finset (Ideal R)) : Set (Ideal R) :=
  (fun J : Ideal R => J.radical) '' (s : Set (Ideal R))

/**
The associated primes supplied by a primary decomposition.

For a minimal primary decomposition this is exactly `I.associatedPrimes`, by
Mathlib's `image_radical_eq_associated_primes` theorem.
*/
abbrev associatedPrimesOfPrimaryDecomposition (I : Ideal R) (s : Finset (Ideal R)) :
    Set (Ideal R) :=
  primaryDecompositionPrimes I s

/**
An isolated prime of a primary decomposition.

This is a minimal element of the set of radicals of its primary components.
The definition uses Mathlib's order-theoretic `Minimal` predicate.
*/
def isolatedPrime (I : Ideal R) (s : Finset (Ideal R)) (p : Ideal R) : Prop :=
  Minimal (· ∈ primaryDecompositionPrimes I s) p

/**
An embedded prime of a primary decomposition.

This is a prime attached to a component that is not isolated.
*/
def embeddedPrime (I : Ideal R) (s : Finset (Ideal R)) (p : Ideal R) : Prop :=
  p ∈ primaryDecompositionPrimes I s ∧ ¬isolatedPrime I s p

end Ideal

end LeanCategories.Algebra

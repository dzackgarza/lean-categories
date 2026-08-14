/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Lasker

@[expose] public section

namespace LeanCategories.Algebra

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

/-! ### Primary decompositions -/

/-- An arbitrary finite primary decomposition of an ideal. -/
def IsPrimaryDecomposition (I : Ideal R) (s : Finset (Ideal R)) : Prop :=
  s.inf id = I ∧ ∀ ⦃J : Ideal R⦄, J ∈ s → J.IsPrimary

/-- The prime candidates attached to a primary decomposition. -/
def primaryDecompositionPrimes (I : Ideal R) (s : Finset (Ideal R)) : Set (Ideal R) :=
  (fun J : Ideal R => J.radical) '' (s : Set (Ideal R))

/-- An isolated prime of a primary decomposition. -/
def isolatedPrime (I : Ideal R) (s : Finset (Ideal R)) (p : Ideal R) : Prop :=
  Minimal (· ∈ primaryDecompositionPrimes I s) p

/-- An embedded prime of a primary decomposition. -/
def embeddedPrime (I : Ideal R) (s : Finset (Ideal R)) (p : Ideal R) : Prop :=
  p ∈ primaryDecompositionPrimes I s ∧ ¬isolatedPrime I s p

end Ideal

end LeanCategories.Algebra

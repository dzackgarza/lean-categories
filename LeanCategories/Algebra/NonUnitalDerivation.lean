/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra

/-!
# Derivations of nonunital nonassociative algebras

Humphreys FC14-C01-U014. The source definition is the carrier of linear
endomorphisms satisfying Leibniz. Vector-subspace and commutator-closure
statements are result content.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u v

variable (R : Type u) (A : Type v)
variable [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- Linear endomorphisms satisfying Humphreys' derivation equation. -/
def nonUnitalDerivationSet : Set (Module.End R A) :=
  {D | ∀ a b : A, D (a * b) = a * D b + D a * b}

/-- The raw type `Der(A)` of derivations, before adding the theorem-level
vector-space and Lie-subalgebra structures. -/
abbrev NonUnitalDerivation : Type _ :=
  nonUnitalDerivationSet R A

end LeanCategories.Algebra

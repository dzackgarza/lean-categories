/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Finite abelian invariant-factor data

Canonical data for the invariant-factor presentation of a finite abelian group.

The divisibility convention follows Dummit--Foote, *Abstract Algebra*, 3rd ed.,
§5.2: for factors `(n₁, ..., nₛ)`, each `nᵢ₊₁ ∣ nᵢ` and every factor is at
least `2`.
-/

@[expose] public section

namespace LeanCategories.Algebra

/-- An invariant-factor type `(n₁, ..., nₛ)` for a finite abelian group.

The factors are nontrivial and ordered so that each later factor divides the
preceding one, matching Dummit--Foote §5.2. -/
structure FiniteAbelianType where
  factors : List ℕ
  factors_gt_one : ∀ n ∈ factors, 1 < n
  divisibility : List.IsChain (fun a b => b ∣ a) factors

namespace FiniteAbelianType

/-- The cyclic product represented by invariant-factor data. -/
abbrev realization (t : FiniteAbelianType) : Type :=
  (i : Fin t.factors.length) → Multiplicative (ZMod (t.factors.get i))

/-- The order represented by invariant-factor data. -/
def order (t : FiniteAbelianType) : ℕ := t.factors.prod

/-- Invariant-factor data representing groups of a prescribed finite order. -/
abbrev OfOrder (n : ℕ) := {t : FiniteAbelianType // t.order = n}

end FiniteAbelianType

namespace CommGroup

/-- A commutative group is *of type* `t` when it is isomorphic to the cyclic
product specified by the invariant factors `t`.

This is Dummit--Foote FC01-C05-U009. It intentionally stores no chosen
isomorphism. -/
def IsOfFiniteAbelianType (G : Type*) [CommGroup G] (t : FiniteAbelianType) : Prop :=
  Nonempty (G ≃* t.realization)

end CommGroup

end LeanCategories.Algebra

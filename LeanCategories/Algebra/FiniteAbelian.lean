/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Factorization.PrimePow
public import Mathlib.GroupTheory.Exponent
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

/-- The rank of a finite abelian invariant-factor type. -/
def rank (t : FiniteAbelianType) : ℕ := t.factors.length

/-- Invariant-factor data representing groups of a prescribed finite order. -/
abbrev OfOrder (n : ℕ) := {t : FiniteAbelianType // t.order = n}

end FiniteAbelianType


/-- Elementary-divisor data for a finite abelian group.  Each factor is a
nontrivial prime power; order is irrelevant at the level of the mathematical
data, so the factors are stored as a multiset. -/
structure FiniteAbelianElementaryDivisors where
  factors : Multiset ℕ
  primePower : ∀ n ∈ factors, IsPrimePow n

namespace FiniteAbelianElementaryDivisors

/-- The order represented by elementary-divisor data. -/
def order (d : FiniteAbelianElementaryDivisors) : ℕ := d.factors.prod

/-- Concatenation of elementary-divisor data. -/
def append (a b : FiniteAbelianElementaryDivisors) : FiniteAbelianElementaryDivisors where
  factors := a.factors + b.factors
  primePower := by
    intro n hn
    rcases Multiset.mem_add.mp hn with hn | hn
    · exact a.primePower n hn
    · exact b.primePower n hn

/-- The elementary divisors contributed by one invariant factor. -/
def ofInvariantFactor (n : ℕ) : FiniteAbelianElementaryDivisors where
  factors := n.primeFactors.val.map fun p => p ^ n.factorization p
  primePower := by
    intro q hq
    rcases Multiset.mem_map.mp hq with ⟨p, hp, rfl⟩
    have hp' : p ∈ n.primeFactors := Finset.mem_def.mpr hp
    rcases Nat.mem_primeFactors.mp hp' with ⟨hpp, hpdvd, hn0⟩
    exact (isPrimePow_nat_iff _).mpr
      ⟨p, n.factorization p, hpp, hpp.factorization_pos_of_dvd hn0 hpdvd, rfl⟩

def ofInvariantFactors : List ℕ → FiniteAbelianElementaryDivisors
  | [] => ⟨0, by simp⟩
  | n :: factors => append (ofInvariantFactor n) (ofInvariantFactors factors)

end FiniteAbelianElementaryDivisors

namespace FiniteAbelianType

/-- Convert invariant factors to their elementary divisors by prime-power
factorization, as in Dummit--Foote FC01-C05-U016. -/
def toElementaryDivisors (t : FiniteAbelianType) : FiniteAbelianElementaryDivisors :=
  FiniteAbelianElementaryDivisors.ofInvariantFactors t.factors

end FiniteAbelianType

namespace CommGroup

/-- A commutative group is *of type* `t` when it is isomorphic to the cyclic
product specified by the invariant factors `t`.

This is Dummit--Foote FC01-C05-U009. It intentionally stores no chosen
isomorphism. -/
def IsOfFiniteAbelianType (G : Type*) [CommGroup G] (t : FiniteAbelianType) : Prop :=
  Nonempty (G ≃* t.realization)

/-- A commutative group has elementary divisors `d` when it admits a cyclic
prime-power decomposition whose multiset of factors is exactly `d`.

The list is only an enumeration witnessing the finite product; equality to the
multiset removes any dependence on the chosen enumeration.  This realizes
Dummit--Foote FC01-C05-U013 without baking the uniqueness theorem into the
definition. -/
def HasElementaryDivisors (G : Type*) [CommGroup G]
    (d : FiniteAbelianElementaryDivisors) : Prop :=
  ∃ factors : List ℕ,
    (↑factors : Multiset ℕ) = d.factors ∧
      Nonempty (G ≃* ((i : Fin factors.length) → Multiplicative (ZMod (factors.get i))))

end CommGroup

end LeanCategories.Algebra

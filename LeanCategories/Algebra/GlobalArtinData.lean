/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Global Artin product data

Definition-level realization of Serre FC10-C14-U048.

For a finite abelian extension, Serre defines the global reciprocity map as the
product of the local Artin symbols.  The preceding local theory proves that for
each idele the local symbols are trivial at all but finitely many places.

Sweep III records the product prescription directly as Mathlib's finite
product over the place-indexed family.  The preceding local theory is still
needed later to show that this total construction agrees with the ordinary
finite product on the actual support and has the expected homomorphism laws.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v w

/-- Exact graph condition for Serre's global Artin map.

`component v a` is the v-component of an idele and `localArtin v` is the
supplied local reciprocity symbol at v.  Whenever a finite set contains the
support of the resulting local symbols, the global value is their product. -/
def IsGlobalArtinMapData
    {Place : Type u} {Idele : Type v}
    {Local : Place → Type w} {G : Type*} [CommGroup G]
    (component : ∀ v, Idele → Local v)
    (localArtin : ∀ v, Local v → G)
    (globalArtin : Idele → G) : Prop := by
  classical
  exact ∀ a S,
    (∀ v, v ∉ S → localArtin v (component v a) = 1) →
      globalArtin a = ∏ v ∈ S, localArtin v (component v a)

/-- Serre's global Artin map, constructed directly as the finite product of
the local Artin symbols over all places.

Mathlib's `finprod` is a total operation.  The theorem that an idele has only
finitely many nontrivial local Artin symbols identifies this value with
Serre's ordinary finite product and is not an input to the definition. -/
def globalArtinMapData
    {Place : Type u} {Idele : Type v}
    {Local : Place → Type w} {G : Type*} [CommGroup G]
    (component : ∀ v, Idele → Local v)
    (localArtin : ∀ v, Local v → G)
    (a : Idele) : G :=
  ∏ᶠ v, localArtin v (component v a)

end LeanCategories.Algebra

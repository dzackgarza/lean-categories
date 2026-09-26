/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Global Artin product data

Definition-level realization of Serre FC10-C14-U048.

For a finite abelian extension, Serre defines the global reciprocity map as the
product of the local Artin symbols.  The preceding local theory proves that for
each idele the local symbols are trivial at all but finitely many places.

Sweep III records the product prescription without proving that finite-support
result: a candidate global map is characterized by agreeing with the product
over every finite set outside which the supplied local symbols are trivial.
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

/-- Source-faithful global Artin-map data: a function together with Serre's
exact finite-product graph for the supplied local symbols.

Almost-all-triviality and independence of the controlling finite set supply
existence later; no arbitrary global function is selected beforehand. -/
abbrev GlobalArtinMapData
    {Place : Type u} {Idele : Type v}
    {Local : Place → Type w} {G : Type*} [CommGroup G]
    (component : ∀ v, Idele → Local v)
    (localArtin : ∀ v, Local v → G) :=
  {globalArtin : Idele → G //
    IsGlobalArtinMapData component localArtin globalArtin}

end LeanCategories.Algebra

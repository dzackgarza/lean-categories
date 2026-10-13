/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Field-indexing data for class formations

Definition-level realization of Serre FC10-C11-U001.

Serre starts the class-formation formalism with a family of finite-index
subgroups that is closed under finite intersections, overgroups, and
conjugation. This file records exactly those four clauses as predicates on
the subgroup family. No Galois terminology, formation cohomology, or class
formation axioms are introduced here.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u v

variable {G : Type u} [Group G]

/-- Serre's field-indexing axioms for the subgroup family in a formation
(FC10-C11-U001).

The family consists of finite-index subgroups, is closed under arbitrary
finite intersections, contains every overgroup of each member, and is stable
under conjugation by the ambient group. -/
def IsFormationSubgroupFamily (family : Set (Subgroup G)) : Prop :=
  (∀ H : Subgroup G, H ∈ family → H.FiniteIndex) ∧
    (∀ S : Set (Subgroup G), S.Finite → S ⊆ family → sInf S ∈ family) ∧
    (∀ H : Subgroup G, H ∈ family →
      ∀ K : Subgroup G, H ≤ K → K ∈ family) ∧
    (∀ H : Subgroup G, H ∈ family →
      ∀ g : G, H.map (MulAut.conj g).toMonoidHom ∈ family)

/-- Indexed form of `IsFormationSubgroupFamily`, matching Serre's notation
`{G_E}_{E∈X}`. -/
def IsFormationIndexingFamily {X : Type v} (G_E : X → Subgroup G) : Prop :=
  IsFormationSubgroupFamily (Set.range G_E)

end LeanCategories.Homological

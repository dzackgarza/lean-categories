/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Raw norm-topology data for class formations

Definition-level realization of Serre, *Local Fields*, Chapter XI,
`FC10-C11-U019`.

Serre's norm topology is the group topology for which the norm subgroups form
a neighbourhood basis at the identity. Sweep III records that basis condition
and the resulting open-set predicate directly, without packaging a
`TopologicalSpace` or proving the topology/group-topology axioms.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u

variable {A : Type u} [Group A]

/-- A set is a neighbourhood of the identity for the raw norm-topology data
when it contains one of the designated norm subgroups. -/
def IsFormationNormNeighborhoodData
    (normSubgroups : Set (Subgroup A)) (U : Set A) : Prop :=
  ∃ N : Subgroup A, N ∈ normSubgroups ∧ (N : Set A) ⊆ U

/-- Serre's raw norm-open predicate: every point of `U` has a left translate
of one of the designated norm subgroups contained in `U`.

Showing that this predicate satisfies the topology axioms and makes the group
operations continuous is result content. -/
def IsFormationNormOpenData
    (normSubgroups : Set (Subgroup A)) (U : Set A) : Prop :=
  ∀ x : A, x ∈ U →
    ∃ N : Subgroup A, N ∈ normSubgroups ∧
      ∀ n : A, n ∈ N → x * n ∈ U

/-- The source-level raw data of a norm topology: its family of norm
subgroups together with the induced neighbourhood/open predicates. -/
structure FormationNormTopologyData (A : Type u) [Group A] where
  normSubgroups : Set (Subgroup A)

namespace FormationNormTopologyData

/-- Neighbourhood predicate attached to raw norm-topology data. -/
abbrev IsNeighborhood (T : FormationNormTopologyData A) : Set A → Prop :=
  IsFormationNormNeighborhoodData T.normSubgroups

/-- Open-set predicate attached to raw norm-topology data. -/
abbrev IsOpen (T : FormationNormTopologyData A) : Set A → Prop :=
  IsFormationNormOpenData T.normSubgroups

/-- Serre's universal norm subgroup: the intersection of every designated
norm subgroup (FC10-C11-U026). -/
def universalNormSubgroup (T : FormationNormTopologyData A) : Subgroup A :=
  sInf T.normSubgroups

end FormationNormTopologyData

end LeanCategories.Homological

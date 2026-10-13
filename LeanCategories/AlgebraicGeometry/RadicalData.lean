/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.UnipotentSubgroupData
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Topology.Connected.Basic

/-!
# Solvable and unipotent radical data

Definition-level realizations of Humphreys FC16-C07-U029 and FC16-C07-U030.

The source characterizes the two radicals as the largest connected normal
solvable or unipotent subgroups. Their existence is a theorem.  The
semisimple/reductive predicates below are stated intrinsically, by requiring
every connected normal solvable/unipotent subgroup to be trivial; they
therefore do not take a separately supplied radical object.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A connected normal solvable subgroup of the ambient algebraic group. -/
def IsConnectedNormalSolvableSubgroup (H : Subgroup G) : Prop :=
  IsConnected (H : Set G) ∧ H.Normal ∧ Group.IsSolvable H

/-- The source characterization of the solvable radical: greatest among
connected normal solvable subgroups. -/
def IsSolvableRadical (R : Subgroup G) : Prop :=
  IsGreatest {H : Subgroup G | IsConnectedNormalSolvableSubgroup H} R

/-- Source-faithful solvable-radical data. -/
abbrev SolvableRadicalData :=
  {R : Subgroup G // IsSolvableRadical R}

/-- A connected normal unipotent subgroup relative to the ambient intrinsic
unipotent-element predicate. -/
def IsConnectedNormalUnipotentSubgroup
    (isUnipotentElement : G → Prop) (H : Subgroup G) : Prop :=
  IsConnected (H : Set G) ∧
    H.Normal ∧
    IsUnipotentSubgroup isUnipotentElement H

/-- The source characterization of the unipotent radical: greatest among
connected normal unipotent subgroups. -/
def IsUnipotentRadical
    (isUnipotentElement : G → Prop) (R : Subgroup G) : Prop :=
  IsGreatest
    {H : Subgroup G | IsConnectedNormalUnipotentSubgroup isUnipotentElement H} R

/-- Source-faithful unipotent-radical data relative to the ambient
unipotent-element predicate. -/
abbrev UnipotentRadicalData
    (isUnipotentElement : G → Prop) :=
  {R : Subgroup G // IsUnipotentRadical isUnipotentElement R}

/-- A connected nontrivial algebraic group is semisimple when every connected
normal solvable subgroup is trivial.  This is the radical-triviality
definition stated without supplying the radical as extra input. -/
def IsSemisimpleGroup : Prop :=
  Nontrivial G ∧
    IsConnected (Set.univ : Set G) ∧
    ∀ H : Subgroup G, IsConnectedNormalSolvableSubgroup H → H = ⊥

/-- A connected nontrivial algebraic group is reductive when every connected
normal unipotent subgroup is trivial.  This is the unipotent-radical
triviality definition without a supplied radical witness. -/
def IsReductiveGroup (isUnipotentElement : G → Prop) : Prop :=
  Nontrivial G ∧
    IsConnected (Set.univ : Set G) ∧
    ∀ H : Subgroup G,
      IsConnectedNormalUnipotentSubgroup isUnipotentElement H → H = ⊥

end LeanCategories.AlgebraicGeometry

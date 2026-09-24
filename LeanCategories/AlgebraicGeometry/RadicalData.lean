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
solvable or unipotent subgroups.  Their existence is a theorem.  Following
the Sweep-III construction boundary, this file records the characterizing
predicates and selects the source-named subgroups by `Classical.epsilon`;
no existence or uniqueness result is proved here.
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

/-- The source-named solvable radical, selected from its defining
characterization.  Existence and uniqueness are result-layer facts. -/
noncomputable def solvableRadical : Subgroup G :=
  Classical.epsilon (IsSolvableRadical (G := G))

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

/-- The source-named unipotent radical, selected from its defining
characterization.  Existence and uniqueness are result-layer facts. -/
noncomputable def unipotentRadical
    (isUnipotentElement : G → Prop) : Subgroup G :=
  Classical.epsilon (IsUnipotentRadical isUnipotentElement)

/-- A connected nontrivial algebraic group is semisimple when its solvable
radical is trivial. -/
def IsSemisimpleGroup : Prop :=
  Nontrivial G ∧
    IsConnected (Set.univ : Set G) ∧
    solvableRadical (G := G) = ⊥

/-- A connected nontrivial algebraic group is reductive when its unipotent
radical is trivial. -/
def IsReductiveGroup (isUnipotentElement : G → Prop) : Prop :=
  Nontrivial G ∧
    IsConnected (Set.univ : Set G) ∧
    unipotentRadical isUnipotentElement = ⊥

end LeanCategories.AlgebraicGeometry

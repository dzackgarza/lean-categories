/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Connected.Basic

/-!
# Borel subgroup data

Definition-level realization of Humphreys FC16-C08-U004.

In the classical point-set presentation used by the source, an algebraic
subgroup is a closed subgroup of the ambient algebraic group.  A Borel
subgroup is maximal among those closed subgroups that are connected and
solvable.  The coincidence of Borels of `G` with Borels of `G°` is a
result, not part of the definition.
-/

@[expose] public section

namespace LeanCategories.AlgebraicGeometry

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The defining property of the subgroups among which Borel subgroups are
maximal: closed, connected, and solvable. -/
def IsClosedConnectedSolvableSubgroup (H : Subgroup G) : Prop :=
  IsClosed (H : Set G) ∧
    IsConnected (H : Set G) ∧
    Group.IsSolvable H

/-- A Borel subgroup is a maximal closed connected solvable subgroup. -/
def IsBorelSubgroup (B : Subgroup G) : Prop :=
  Maximal IsClosedConnectedSolvableSubgroup B

end LeanCategories.AlgebraicGeometry

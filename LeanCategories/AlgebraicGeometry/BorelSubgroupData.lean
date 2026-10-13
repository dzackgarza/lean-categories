/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Irreducible

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

/-- The carrier in the ambient group of the irreducible component of the
identity inside a subgroup.  For algebraic subgroups over an algebraically
closed field this is the classical identity-component carrier `H°`. -/
noncomputable def subgroupIdentityComponentCarrier (H : Subgroup G) : Set G :=
  ((↑) : H → G) '' irreducibleComponent (1 : H)

/-- The provisional Cartan-subgroup carrier attached to a torus `T`:
the identity component of its centralizer.

When `T` is maximal this is Humphreys FC16-C08-U015.  Nilpotence and
self-normalizing properties are result-layer statements. -/
noncomputable def cartanSubgroupCarrier (T : Subgroup G) : Set G :=
  subgroupIdentityComponentCarrier (Subgroup.centralizer (T : Set G))

/-- The stable Cartan-subgroup construction of FC16-C08-U021: for a
maximal torus `T`, take its centralizer `C_G(T)`.

Maximality of `T` is source input.  The assertions that every Cartan subgroup
arises this way, that this agrees with the provisional `C_G(T)°` carrier, and
that all Cartan subgroups are conjugate are result-layer statements. -/
def cartanSubgroupOfMaximalTorus (T : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (T : Set G)

end LeanCategories.AlgebraicGeometry

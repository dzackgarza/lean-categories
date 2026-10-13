/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.UnipotentSubgroupData
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Topology.Connected.Basic

/-!
# Root subgroup data

Definition-level realization of the definitional clause in Humphreys
FC16-C09-U033.

For a root `α`, the source characterizes `U_α` as the connected,
`T`-stable, one-dimensional unipotent algebraic subgroup whose Lie algebra
is the root space `g_α`.  Sweep III records that characterization for a
supplied subgroup.  Existence and uniqueness of `U_α`, Weyl conjugacy,
admissible additive-group parametrizations, and generation of the ambient
group are result-layer statements.
-/

@[expose] public section

namespace LeanCategories.AlgebraicGeometry

universe u v w x

variable {K : Type u} [Field K]
variable {G : Type v} [Group G] [TopologicalSpace G]
variable {L : Type w} [AddCommGroup L] [Module K L]
variable {Φ : Type x}

/-- A subgroup `U` is stable under conjugation by a subgroup `T`. -/
def IsConjugationStable (T U : Subgroup G) : Prop :=
  ∀ t : T, ∀ u : U, t.1 * u.1 * (t.1)⁻¹ ∈ U

/-- The definition-level characterization of the root subgroup attached to
`α` relative to `T`.

`isOneDimensional`, `lieAlgebra`, `rootSpace`, and
`isUnipotentElement` are supplied by the preceding dimension, tangent/root,
and Jordan-decomposition layers. -/
def IsRootSubgroup
    (isOneDimensional : Subgroup G → Prop)
    (isUnipotentElement : G → Prop)
    (lieAlgebra : Subgroup G → Submodule K L)
    (rootSpace : Φ → Submodule K L)
    (T : Subgroup G) (α : Φ) (U : Subgroup G) : Prop :=
  IsClosed (U : Set G) ∧
    IsConnected (U : Set G) ∧
    IsConjugationStable T U ∧
    isOneDimensional U ∧
    IsUnipotentSubgroup isUnipotentElement U ∧
    lieAlgebra U = rootSpace α

end LeanCategories.AlgebraicGeometry

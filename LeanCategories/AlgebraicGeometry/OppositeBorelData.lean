/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.BorelSubgroupData

/-!
# Opposite Borel data

Definition-level realization of the definitional clause in Humphreys
FC16-C09-U032.

For a maximal torus `T` and a Borel subgroup `B` containing it, the source
calls a Borel `Bminus` opposite to `B` when their intersection is exactly
`T`.  Existence and uniqueness of such a Borel, and the associated Lie
algebra decomposition, are result-layer statements and are not used here.
-/

@[expose] public section

namespace LeanCategories.AlgebraicGeometry

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A supplied Borel subgroup `Bminus` is opposite to `B` relative to `T`
when `B ∩ Bminus = T`.

The hypotheses that `T` is a maximal torus and `B` is a Borel containing
`T` are preceding source data. -/
def IsOppositeBorelSubgroup
    (T B Bminus : Subgroup G) : Prop :=
  IsBorelSubgroup Bminus ∧ B ⊓ Bminus = T

end LeanCategories.AlgebraicGeometry

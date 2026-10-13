/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.BorelSubgroupData

/-!
# Rank-one and rank-two subgroup data

Definition-level realization of Humphreys FC16-C11-U018.

The source constructs the rank-one and rank-two subgroups used in the
classification by centralizing, respectively, a root-kernel torus and the
identity component of the intersection of two such tori.  Their reductivity,
semisimple rank, root subsystem, and Levi-factor properties are theorem-layer
statements and are not bundled here.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The source subgroup `Z_α = C_G(T_α)`. -/
def rankOneRootCentralizer (Talpha : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (Talpha : Set G)

/-- The source subgroup
`Z_{αβ} = C_G((T_α ∩ T_β)°)`.

The identity component is supplied by the existing algebraic-subgroup
carrier construction; no reductivity or rank theorem is used to form this
centralizer. -/
noncomputable def rankTwoRootCentralizer
    (Talpha Tbeta : Subgroup G) : Subgroup G :=
  Subgroup.centralizer
    (subgroupIdentityComponentCarrier (Talpha ⊓ Tbeta))

end LeanCategories.AlgebraicGeometry

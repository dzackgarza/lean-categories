/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.BorelSubgroupData

/-!
# Quasisplit-group data

Definition-level reference port for Humphreys FC16-C12-U031.

A semisimple group over `k` is `k`-quasisplit precisely when it has a Borel
subgroup defined over `k`.  The Borel predicate is supplied by FC16-C08-U004
and the predicate expressing descent/definition over the base by FC16-C12-U006.
No existence or classification theorem is included here.
-/

@[expose] public section

namespace LeanCategories.AlgebraicGeometry

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Witness data for a quasisplit group: a Borel subgroup defined over the
chosen base. -/
structure QuasisplitData
    (isDefinedOverBase : Subgroup G → Prop) where
  B : Subgroup G
  isBorel : IsBorelSubgroup B
  isDefinedOverBase_B : isDefinedOverBase B

/-- A group is quasisplit over the base when some Borel subgroup is defined
over that base.

`isDefinedOverBase` is the descent predicate supplied by the preceding
general-field layer; keeping it explicit avoids replacing a base-defined
Borel by a Borel only after algebraic closure. -/
def IsQuasisplit
    (isDefinedOverBase : Subgroup G → Prop) : Prop :=
  Nonempty (QuasisplitData isDefinedOverBase)

end LeanCategories.AlgebraicGeometry

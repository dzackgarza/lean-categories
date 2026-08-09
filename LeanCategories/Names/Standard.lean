/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.Rings
public import LeanCategories.Core.Ids

@[expose] public section

/-!
# Standard names and spelling aliases

Aliases do not create semantic nodes. `CRings` is recorded as `aliasOf`
`cat.commutative_rings`.
-/

namespace LeanCategories.Names

open LeanCategories

abbrev CommutativeRings := Algebra.Rings.CommutativeRings

/-- Spelling alias — registry id `alias.crings`. -/
abbrev CRings := CategoryId.commutativeRings

example : AliasId.crings.raw = "alias.crings" := by rfl

end LeanCategories.Names

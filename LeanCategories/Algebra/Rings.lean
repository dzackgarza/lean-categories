/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.Magmas
public import LeanCategories.Core.Ids

@[expose] public section

/-!
# Rings cluster

Owns the two-operation host interface and ring names. Does **not** redeclare
`Commutative` as a ring classifier — applies the magma classifier along the
multiplicative port.
-/

namespace LeanCategories.Algebra.Rings

open LeanCategories
open Algebra.Magmas

/-- The two-operation host is intentionally opaque at this presentation layer. -/
def MagmasWithTwoOperations : CategoryExpr := .opaque CategoryId.magmasWithTwoOperations

/-- Rings are the refined two-operation tower. -/
def Rings : CategoryExpr :=
  let addAssoc := .refine MagmasWithTwoOperations Associative (some RouteId.additive)
  let addComm := .refine addAssoc Commutative (some RouteId.additive)
  let addUnital := .refine addComm Unital (some RouteId.additive)
  let addInv := .refine addUnital Inverse (some RouteId.additive)
  let mulAssoc := .refine addInv Associative (some RouteId.multiplicative)
  let dist := .refine mulAssoc ClassifierId.m2oDistributive none
  .refine dist Unital (some RouteId.multiplicative)

/-- CommutativeRings := Rings.Commutative[via := multiplicative]. -/
def CommutativeRings : CategoryExpr :=
  .refine (.atom CategoryId.rings) Commutative (some RouteId.multiplicative)

end LeanCategories.Algebra.Rings

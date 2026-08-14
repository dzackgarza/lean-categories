/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.Catalogue.Magmas
public import LeanCategories.Algebra.Catalogue

@[expose] public section

/-!
# Rings cluster

Owns the two-operation host interface and ring names. Does **not** redeclare
`Commutative` as a ring classifier — applies the magma classifier along the
multiplicative port.
-/

namespace LeanCategories.Algebra.Catalogue.Rings

open LeanCategories
open Algebra.Catalogue.Magmas

/-- The two-operation host is intentionally opaque at this presentation layer. -/
def MagmasWithTwoOperations : CategoryExpr := .opaque CategoryId.magmasWithTwoOperations

/-- Rings remain an atom until the complete multi-port pullback is realized. -/
def Rings : CategoryExpr := .atom CategoryId.rings

/-- Commutative rings remain an atom until their pullback realization exists. -/
def CommutativeRings : CategoryExpr := .atom CategoryId.commutativeRings

def DivisionRings : CategoryExpr :=
  .atom CategoryId.divisionRings

end LeanCategories.Algebra.Catalogue.Rings

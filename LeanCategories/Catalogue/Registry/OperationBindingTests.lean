/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.MonoidOperations
public import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

namespace CasCatalogue

open Lean Meta in
run_meta do
  let state ← semanticState
  let rings := Algebra.Catalogue.Rings.Rings
  let monoids := Algebra.Catalogue.Magmas.Monoids
  let direct : Route := { source := rings, target := rings, steps := #[] }
  unless state.isFirstOperationBindingRoute "·" direct do
    throwError "the explicit ring multiplication binding was not retained"
  let later := state.routes rings monoids
  unless later.size ≥ 2 do
    throwError "the independent additive and multiplicative monoid routes are missing"
  for route in later do
    if state.isFirstOperationBindingRoute "·" route then
      throwError "a farther monoid multiplication replaced the explicit ring binding"
  -- With no binding at the selected ring, both incomparable routes survive.
  -- This interface deliberately makes no order-based choice between them.
  let inherited := { state with operations := state.operations.filter fun entry =>
    entry.id.raw != "op.rings.mul" }
  for route in later do
    unless inherited.isFirstOperationBindingRoute "·" route do
      throwError "an incomparable inherited multiplication binding was discarded"
  let selectedMonoid : Route := { source := monoids, target := monoids, steps := #[] }
  unless state.isFirstOperationBindingRoute "·" selectedMonoid do
    throwError "an explicit monoid view lost its own multiplication binding"

end CasCatalogue

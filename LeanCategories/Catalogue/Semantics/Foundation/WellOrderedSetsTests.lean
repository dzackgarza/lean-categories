/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.WellOrderedSetsRegistration
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.WellOrderedSetsRegistration

/-!
# The rows #97 requires are registered (#97)

The check `lean-cas-dsl#68` reads: the classifier `clf.linear_orders.well_ordered`, the two
categories it names, and the two functor rows `E_mon → WellOrderedSets` and
`Core(WellOrderedSets) → Ordinals`, each with the declaration and the endpoints the row is supposed
to expose. A row that was dropped, silently changed its declaration, or was given the wrong
endpoints fails here.
-/

@[expose] public section

namespace CasCatalogue

open Lean Meta in
run_meta do
  let state ← semanticState
  let some classifier := state.classifier? ClassifierId.setsWellOrdered
    | throwError "#97: the well-ordered-set classifier is not registered"
  unless classifier.declaration == `LeanCategories.Foundation.wellOrderedSets do
    throwError "#97: the classifier row exposes {classifier.declaration}"
  let some total := state.category? Foundation.WellOrderedSetCatalogue.WellOrderedSets
    | throwError "#97: cat.well_ordered_sets is not registered"
  unless total.declaration == `LeanCategories.Foundation.WellOrderedSets do
    throwError "#97: the well-ordered-set category row exposes {total.declaration}"
  let some core := state.category? Foundation.WellOrderedSetCatalogue.CoreWellOrderedSets
    | throwError "#97: the core of the well-ordered sets is not registered"
  let some monotone := state.category? Foundation.WellOrderedSetCatalogue.EnumeratedMonotoneSets
    | throwError "#97: cat.enumerated_monotone_sets is not registered"
  unless monotone.declaration == `LeanCategories.Foundation.EnumeratedMonotoneSets do
    throwError "#97: the E_mon row exposes {monotone.declaration}"
  let some induced := state.functor? FunctorId.enumeratedMonotoneToWellOrdered
    | throwError "#97: the E_mon → WellOrderedSets row is missing"
  unless induced.declaration == `LeanCategories.Foundation.enumeratedMonotoneToWellOrdered do
    throwError "#97: the E_mon → WellOrderedSets row exposes {induced.declaration}"
  unless induced.source.syntacticEq monotone.expression do
    throwError "#97: the E_mon → WellOrderedSets row has the wrong source"
  unless induced.target.syntacticEq total.expression do
    throwError "#97: the E_mon → WellOrderedSets row has the wrong target"
  let some linearOrder := state.functor? FunctorId.wellOrderedToLinearOrder
    | throwError "#97: the forgetful route to the linear orders is missing"
  unless linearOrder.declaration ==
      `CasCatalogue.Foundation.WellOrderedSets.wellOrderedToLinearOrderDeclaration do
    throwError "#97: the forgetful route exposes {linearOrder.declaration}"
  unless linearOrder.source.syntacticEq total.expression do
    throwError "#97: the forgetful route has the wrong source"
  unless linearOrder.target.syntacticEq Foundation.TotallyOrderedSets do
    throwError "#97: the forgetful route has the wrong target"
  let some inclusion := state.functor? FunctorId.enumeratedMonotoneInclusion
    | throwError "#97: the identity-on-objects inclusion E_mon → E is missing"
  unless inclusion.source.syntacticEq monotone.expression do
    throwError "#97: the inclusion E_mon → E has the wrong source"
  unless inclusion.target.syntacticEq Foundation.EnumeratedSets do
    throwError "#97: the inclusion E_mon → E has the wrong target"
  let some orderType := state.functor? FunctorId.orderType
    | throwError "#97: the order-type row is missing"
  unless orderType.source.syntacticEq core.expression do
    throwError "#97: the order-type row does not have the core as its domain"
  unless orderType.target.syntacticEq Foundation.Ordinals.Ordinals do
    throwError "#97: the order-type row does not have Ordinals as its codomain"

end CasCatalogue

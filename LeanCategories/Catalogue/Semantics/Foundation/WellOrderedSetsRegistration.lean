/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.Foundation.WellOrderedSets
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.WellOrderedSets

/-!
# Registry rows for well-ordered sets and the enumeration-to-order contract (#97)

The rows `lean-cas-dsl#68` reads for this unit, each naming the Lean declaration it exposes:

* `clf.linear_orders.well_ordered` -- `LeanCategories.Foundation.wellOrderedSets`, the property
  subcategory of the linear orders on `IsWellOrder X (· < ·)`.
* `cat.well_ordered_sets` -- `LeanCategories.Foundation.WellOrderedSets`, its total: sets with a
  selected well-order and monotone maps.
* `cat.enumerated_monotone_sets` -- `LeanCategories.Foundation.EnumeratedMonotoneSets`, the wide
  subcategory `E_mon` of the enumerated sets, with all the objects of `E` and the monotone maps.
* `fun.enumerated_monotone_sets.well_ordered_sets` --
  `LeanCategories.Foundation.enumeratedMonotoneToWellOrdered`, the functor `E_mon → WellOrderedSets`
  that sends an object to its induced selected order.
* `fun.well_ordered_sets.order_type` --
  `LeanCategories.Foundation.WellOrderedSetCat.orderTypeFunctor`, the order-type functor
  `Core(WellOrderedSets) → Ordinals`, whose domain is the core and not all monotone maps.

The supporting rows name the forgetful classifer and the identity-on-objects inclusion `E_mon → E`.
The existing all-function `EnumeratedSets` category is unchanged and is the target of that
inclusion; no row asserts a functor from all of `E` to `WellOrderedSets`.
-/

@[expose] public section

open CategoryTheory

namespace CasCatalogue.Foundation.WellOrderedSets

open LeanCategories LeanCategories.Foundation
open CasCatalogue.Foundation.WellOrderedSetCatalogue

universe u

/-- The classifier whose total is `WellOrderedSets`: the well-ordered sets as the property
subcategory of the linear orders, with `toLinearOrder` its forgetful functor. -/
noncomputable def wellOrderedClassifierRealization :
    ClassifierRealization Foundation.TotallyOrderedSets ClassifierId.setsWellOrdered
      LeanCategories.Foundation.TotallyOrderedSets.{u}
      LeanCategories.Foundation.wellOrderedSets.{u} :=
  { hostRealization :=
      CasCatalogue.Foundation.CatalogueRegistration.totallyOrderedSetsCategoryRealization
    totalRealization := { familyFibre := none } }

/-- The total of that classifier, as a registered category. -/
noncomputable def wellOrderedSetsRealization :
    CategoryRealization (.classifierTotal ClassifierId.setsWellOrdered)
      LeanCategories.Foundation.WellOrderedSets.{u} :=
  { familyFibre := none }

/-- The core of the well-ordered sets, as a bundled category. -/
noncomputable def coreWellOrderedSetsCategory :=
  Constructors.core LeanCategories.Foundation.WellOrderedSets.{u}

noncomputable def coreWellOrderedSetsRealization :
    CategoryRealization CoreWellOrderedSets coreWellOrderedSetsCategory.{u} :=
  { familyFibre := none }

noncomputable def enumeratedMonotoneSetsRealization :
    CategoryRealization EnumeratedMonotoneSets
      LeanCategories.Foundation.EnumeratedMonotoneSets.{u} :=
  { familyFibre := none }

/-- `WellOrderedSets → LinOrd`: the classifier's own forgetful functor, typed for the registry. -/
noncomputable def wellOrderedToLinearOrderDeclaration :
    LeanCategories.Foundation.WellOrderedSets.{u} ⥤
      LeanCategories.Foundation.TotallyOrderedSets.{u} :=
  LeanCategories.Foundation.WellOrderedSetCat.toLinearOrder

noncomputable def wellOrderedToLinearOrderRealization :
    FunctorRealization WellOrderedToLinearOrderExpr
      LeanCategories.Foundation.WellOrderedSets.{u}
      LeanCategories.Foundation.TotallyOrderedSets.{u}
      wellOrderedToLinearOrderDeclaration :=
  { sourceRealization := wellOrderedSetsRealization
    targetRealization :=
      CasCatalogue.Foundation.CatalogueRegistration.totallyOrderedSetsCategoryRealization }

noncomputable def wellOrderedToSetsDeclaration :
    LeanCategories.Foundation.WellOrderedSets.{u} ⥤
      LeanCategories.Foundation.Mathlib.Sets.{u} :=
  LeanCategories.Foundation.wellOrderedToSets

noncomputable def wellOrderedToSetsRealization :
    FunctorRealization WellOrderedToSetsExpr
      LeanCategories.Foundation.WellOrderedSets.{u}
      LeanCategories.Foundation.Mathlib.Sets.{u}
      wellOrderedToSetsDeclaration :=
  { sourceRealization := wellOrderedSetsRealization
    targetRealization := CasCatalogue.Foundation.CatalogueRegistration.setsRealization }

noncomputable def enumeratedMonotoneInclusionRealization :
    FunctorRealization EnumeratedMonotoneInclusionExpr
      LeanCategories.Foundation.EnumeratedMonotoneSets.{u}
      LeanCategories.Foundation.EnumeratedSets.{u}
      LeanCategories.Foundation.enumeratedMonotoneInclusion :=
  { sourceRealization := enumeratedMonotoneSetsRealization
    targetRealization :=
      CasCatalogue.Foundation.CatalogueRegistration.enumeratedSetsCategoryRealization }

noncomputable def enumeratedMonotoneToWellOrderedRealization :
    FunctorRealization EnumeratedMonotoneToWellOrderedExpr
      LeanCategories.Foundation.EnumeratedMonotoneSets.{u}
      LeanCategories.Foundation.WellOrderedSets.{u}
      LeanCategories.Foundation.enumeratedMonotoneToWellOrdered :=
  { sourceRealization := enumeratedMonotoneSetsRealization
    targetRealization := wellOrderedSetsRealization }

/-- The order-type functor on the core, as the registered declaration: its domain is
`Core(WellOrderedSets)` and its codomain the registered `Ordinals` category, both as `ObjCat`s. -/
noncomputable def orderTypeDeclaration :
    (Constructors.core LeanCategories.Foundation.WellOrderedSets.{u}) ⥤
      CasCatalogue.Foundation.Ordinals.ordinalsCategory.{u} :=
  LeanCategories.Foundation.WellOrderedSetCat.orderTypeFunctor

noncomputable def orderTypeRealization :
    FunctorRealization OrderTypeExpr
      (Constructors.core LeanCategories.Foundation.WellOrderedSets.{u})
      CasCatalogue.Foundation.Ordinals.ordinalsCategory.{u} orderTypeDeclaration :=
  { sourceRealization := coreWellOrderedSetsRealization
    targetRealization := CasCatalogue.Foundation.Ordinals.ordinalsRealization }

end CasCatalogue.Foundation.WellOrderedSets

namespace CasCatalogue

normalized_registry .classifier
  { id := ClassifierId.setsWellOrdered
    declaration := `LeanCategories.Foundation.wellOrderedSets
    host := Foundation.TotallyOrderedSets
    realization :=
      `CasCatalogue.Foundation.WellOrderedSets.wellOrderedClassifierRealization }

normalized_registry .category
  { id := CategoryId.wellOrderedSets, name := "WellOrderedSets"
    declaration := `LeanCategories.Foundation.WellOrderedSets
    expression := Foundation.WellOrderedSetCatalogue.WellOrderedSets
    realization := `CasCatalogue.Foundation.WellOrderedSets.wellOrderedSetsRealization }

normalized_registry .category
  { id := CategoryId.enumeratedMonotoneSets, name := "EnumeratedMonotoneSets"
    declaration := `LeanCategories.Foundation.EnumeratedMonotoneSets
    expression := Foundation.WellOrderedSetCatalogue.EnumeratedMonotoneSets
    realization := `CasCatalogue.Foundation.WellOrderedSets.enumeratedMonotoneSetsRealization }

normalized_registry .functor
  { id := FunctorId.wellOrderedToLinearOrder
    source := Foundation.WellOrderedSetCatalogue.WellOrderedSets
    target := Foundation.TotallyOrderedSets
    declaration := `CasCatalogue.Foundation.WellOrderedSets.wellOrderedToLinearOrderDeclaration
    realization :=
      `CasCatalogue.Foundation.WellOrderedSets.wellOrderedToLinearOrderRealization
    expression := Foundation.WellOrderedSetCatalogue.WellOrderedToLinearOrderExpr }

normalized_registry .functor
  { id := FunctorId.wellOrderedToSets
    source := Foundation.WellOrderedSetCatalogue.WellOrderedSets
    target := Foundation.Sets
    declaration := `CasCatalogue.Foundation.WellOrderedSets.wellOrderedToSetsDeclaration
    realization := `CasCatalogue.Foundation.WellOrderedSets.wellOrderedToSetsRealization
    expression := Foundation.WellOrderedSetCatalogue.WellOrderedToSetsExpr }

normalized_registry .functor
  { id := FunctorId.enumeratedMonotoneInclusion
    source := Foundation.WellOrderedSetCatalogue.EnumeratedMonotoneSets
    target := Foundation.EnumeratedSets
    declaration := `LeanCategories.Foundation.enumeratedMonotoneInclusion
    realization :=
      `CasCatalogue.Foundation.WellOrderedSets.enumeratedMonotoneInclusionRealization
    expression := Foundation.WellOrderedSetCatalogue.EnumeratedMonotoneInclusionExpr }

normalized_registry .functor
  { id := FunctorId.enumeratedMonotoneToWellOrdered
    source := Foundation.WellOrderedSetCatalogue.EnumeratedMonotoneSets
    target := Foundation.WellOrderedSetCatalogue.WellOrderedSets
    declaration := `LeanCategories.Foundation.enumeratedMonotoneToWellOrdered
    realization :=
      `CasCatalogue.Foundation.WellOrderedSets.enumeratedMonotoneToWellOrderedRealization
    expression := Foundation.WellOrderedSetCatalogue.EnumeratedMonotoneToWellOrderedExpr }

normalized_registry .category
  { id := CategoryId.coreWellOrderedSets
    declaration := `CasCatalogue.Foundation.WellOrderedSets.coreWellOrderedSetsCategory
    expression := Foundation.WellOrderedSetCatalogue.CoreWellOrderedSets
    realization := `CasCatalogue.Foundation.WellOrderedSets.coreWellOrderedSetsRealization }

normalized_registry .functor
  { id := FunctorId.orderType
    source := Foundation.WellOrderedSetCatalogue.CoreWellOrderedSets
    target := Foundation.Ordinals.Ordinals
    declaration := `CasCatalogue.Foundation.WellOrderedSets.orderTypeDeclaration
    realization := `CasCatalogue.Foundation.WellOrderedSets.orderTypeRealization
    expression := Foundation.WellOrderedSetCatalogue.OrderTypeExpr }

end CasCatalogue

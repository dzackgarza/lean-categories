/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Id
public import LeanCategories.Catalogue.Syntax
public import LeanCategories.Catalogue.Semantics.ConstructorCatalogue
public import LeanCategories.Catalogue.Semantics.Foundation.Expressions
public import LeanCategories.Catalogue.Semantics.Foundation.Ordinals
public import LeanCategories.Foundation.EnumeratedMonotone

/-!
# Catalogue vocabulary for well-ordered sets and the enumeration-to-order contract (#97)

The identifiers and symbolic expressions the rows of
`Foundation/WellOrderedSetsRegistration.lean` name.

`WellOrderedSets` is a **classifier total** on the linear orders, not an atom: the well-ordered sets
are the property subcategory of `LinOrd` on `IsWellOrder X (· < ·)`, and the registry records
property subcategories as classifiers on their host (`LeanCategories.Foundation.wellOrderedSets`,
whose total and forgetful functor are `Classifier.ofProperty`'s). The enumeration side is an atom,
because `E_mon` is a wide subcategory of the enumerated sets rather than a property subcategory of
another registered category.
-/

@[expose] public section

open CategoryTheory

namespace CasCatalogue

namespace ClassifierId
/-- Sets carrying a selected linear order whose strict order is a well-order. -/
def setsWellOrdered : ClassifierId := ⟨"clf.linear_orders.well_ordered"⟩
end ClassifierId

namespace CategoryId
/-- Well-ordered sets and monotone maps: the total of the well-ordered-set classifier. -/
def wellOrderedSets : CategoryId := ⟨"cat.well_ordered_sets"⟩
/-- The core of the well-ordered sets: all of them, and only their order isomorphisms. -/
def coreWellOrderedSets : CategoryId := ⟨"cat.core_well_ordered_sets"⟩
/-- The wide subcategory of enumerated sets whose maps are monotone for the selected orders. -/
def enumeratedMonotoneSets : CategoryId := ⟨"cat.enumerated_monotone_sets"⟩
end CategoryId

namespace FunctorId
def wellOrderedToLinearOrder : FunctorId := ⟨"fun.well_ordered_sets.linear_order"⟩
def wellOrderedToSets : FunctorId := ⟨"fun.well_ordered_sets.sets"⟩
def enumeratedMonotoneInclusion : FunctorId := ⟨"fun.enumerated_monotone_sets.enumerated"⟩
def enumeratedMonotoneToWellOrdered : FunctorId :=
  ⟨"fun.enumerated_monotone_sets.well_ordered_sets"⟩
def orderType : FunctorId := ⟨"fun.well_ordered_sets.order_type"⟩
end FunctorId

namespace Foundation.WellOrderedSetCatalogue

open LeanCategories LeanCategories.Foundation

def WellOrderedSets : CategoryExpr := .classifierTotal ClassifierId.setsWellOrdered

/-- `Core(WellOrderedSets)`: all well-ordered sets, and only their order isomorphisms. -/
def CoreWellOrderedSets : CategoryExpr := .construct ConstructorId.core #[.category WellOrderedSets]

def EnumeratedMonotoneSets : CategoryExpr := .atom CategoryId.enumeratedMonotoneSets

def WellOrderedToLinearOrderExpr : FunctorExpr WellOrderedSets Foundation.TotallyOrderedSets :=
  .atomic FunctorId.wellOrderedToLinearOrder

def WellOrderedToSetsExpr : FunctorExpr WellOrderedSets Foundation.Sets :=
  .atomic FunctorId.wellOrderedToSets

def EnumeratedMonotoneInclusionExpr :
    FunctorExpr EnumeratedMonotoneSets Foundation.EnumeratedSets :=
  .atomic FunctorId.enumeratedMonotoneInclusion

def EnumeratedMonotoneToWellOrderedExpr : FunctorExpr EnumeratedMonotoneSets WellOrderedSets :=
  .atomic FunctorId.enumeratedMonotoneToWellOrdered

def OrderTypeExpr : FunctorExpr CoreWellOrderedSets Foundation.Ordinals.Ordinals :=
  .atomic FunctorId.orderType

end Foundation.WellOrderedSetCatalogue

end CasCatalogue

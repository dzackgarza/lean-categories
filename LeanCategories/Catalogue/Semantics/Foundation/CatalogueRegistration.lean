module

public import LeanCategories.Catalogue.Registry.Semantic
public import LeanCategories.Catalogue.Semantics.Foundation.Expressions
public import LeanCategories.Foundation.Mathlib
public import LeanCategories.Foundation.Sets
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Expressions
public meta import LeanCategories.Catalogue.Semantics.Foundation.Catalogue

@[expose] public section

namespace CasCatalogue.Foundation.CatalogueRegistration
open LeanCategories LeanCategories.Foundation

open CategoryTheory
open LeanCategories CasCatalogue

universe u

noncomputable def setsRealization :
    CategoryRealization Foundation.Sets Foundation.Mathlib.Sets :=
  { familyFibre := none }

noncomputable def finiteRealization :
    ClassifierRealization Foundation.Sets ClassifierId.setsFinite
      Foundation.Mathlib.Sets Foundation.Mathlib.finite :=
  { hostRealization := setsRealization, totalRealization := {} }

noncomputable def gradedRealization :
    ClassifierRealization Foundation.Sets ClassifierId.setsGraded
      Foundation.Mathlib.Sets Foundation.Mathlib.graded :=
  { hostRealization := setsRealization, totalRealization := {} }

noncomputable def binaryOperationRealization :
    ClassifierRealization Foundation.Sets ClassifierId.setsBinaryOperation
      Foundation.Mathlib.Sets Foundation.Mathlib.binaryOperation :=
  { hostRealization := setsRealization, totalRealization := {} }

noncomputable def countableRealization :
    ClassifierRealization Foundation.Sets ClassifierId.setsCountable
      Foundation.Mathlib.Sets Foundation.countableSets :=
  { hostRealization := setsRealization, totalRealization := {} }

noncomputable def enumeratedRealization :
    ClassifierRealization Foundation.Sets ClassifierId.setsEnumerated
      Foundation.Mathlib.Sets Foundation.enumeratedSets :=
  { hostRealization := setsRealization, totalRealization := {} }

def countableSetsCategoryRealization :
    CategoryRealization Foundation.CountableSets LeanCategories.Foundation.CountableSets.{u} := {}

def enumeratedSetsCategoryRealization :
    CategoryRealization Foundation.EnumeratedSets LeanCategories.Foundation.EnumeratedSets.{u} := {}

noncomputable def finiteToCountableRealization :
    FunctorRealization Foundation.FiniteToCountableExpr
      Foundation.Mathlib.FiniteSets Foundation.countableSets.total
      Foundation.finiteToCountable :=
  { sourceRealization := {}
    targetRealization := {} }

noncomputable def enumeratedToCountableRealization :
    FunctorRealization Foundation.EnumeratedToCountableExpr
      Foundation.enumeratedSets.total Foundation.countableSets.total
      Foundation.enumeratedToCountable :=
  { sourceRealization := {}
    targetRealization := {} }

noncomputable def setsIdentity : Foundation.Mathlib.Sets ⟶ Foundation.Mathlib.Sets :=
  CategoryStruct.id _

def setsIdentityExpr : FunctorExpr Foundation.Sets Foundation.Sets :=
  .identity Foundation.Sets

noncomputable def setsIdentityRealization :
    FunctorRealization setsIdentityExpr Foundation.Mathlib.Sets
      Foundation.Mathlib.Sets setsIdentity.toFunctor :=
  { sourceRealization := setsRealization, targetRealization := setsRealization }

normalized_registry .category
  { id := CategoryId.sets, name := "Sets"
    declaration := `LeanCategories.Foundation.Mathlib.Sets
    expression := Foundation.Sets
    realization := `CasCatalogue.Foundation.CatalogueRegistration.setsRealization}

normalized_registry .classifier
  { id := ClassifierId.setsFinite
    declaration := `LeanCategories.Foundation.Mathlib.finite
    host := Foundation.Sets
    realization := `CasCatalogue.Foundation.CatalogueRegistration.finiteRealization}

normalized_registry .classifier
  { id := ClassifierId.setsGraded
    declaration := `LeanCategories.Foundation.Mathlib.graded
    host := Foundation.Sets
    realization := `CasCatalogue.Foundation.CatalogueRegistration.gradedRealization}

normalized_registry .classifier
  { id := ClassifierId.setsBinaryOperation
    declaration := `LeanCategories.Foundation.Mathlib.binaryOperation
    host := Foundation.Sets
    realization := `CasCatalogue.Foundation.CatalogueRegistration.binaryOperationRealization}

normalized_registry .classifier
  { id := ClassifierId.setsCountable
    declaration := `LeanCategories.Foundation.countableSets
    host := Foundation.Sets
    realization := `CasCatalogue.Foundation.CatalogueRegistration.countableRealization}

normalized_registry .classifier
  { id := ClassifierId.setsEnumerated
    declaration := `LeanCategories.Foundation.enumeratedSets
    host := Foundation.Sets
    realization := `CasCatalogue.Foundation.CatalogueRegistration.enumeratedRealization}

normalized_registry .category
  { id := CategoryId.countableSets, name := "CountableSets"
    declaration := `LeanCategories.Foundation.CountableSets
    expression := Foundation.CountableSets
    realization := `CasCatalogue.Foundation.CatalogueRegistration.countableSetsCategoryRealization }

normalized_registry .category
  { id := CategoryId.enumeratedSets, name := "EnumeratedSets"
    declaration := `LeanCategories.Foundation.EnumeratedSets
    expression := Foundation.EnumeratedSets
    realization :=
      `CasCatalogue.Foundation.CatalogueRegistration.enumeratedSetsCategoryRealization }

normalized_registry .functor
  { id := FunctorId.setsIdentity
    source := Foundation.Sets
    target := Foundation.Sets
    declaration := `CasCatalogue.Foundation.CatalogueRegistration.setsIdentity
    realization := `CasCatalogue.Foundation.CatalogueRegistration.setsIdentityRealization
    expression := setsIdentityExpr }

normalized_registry .functor
  { id := FunctorId.finiteToCountable
    source := .classifierTotal ClassifierId.setsFinite
    target := Foundation.CountableSets
    declaration := `LeanCategories.Foundation.finiteToCountable
    realization := `CasCatalogue.Foundation.CatalogueRegistration.finiteToCountableRealization
    expression := Foundation.FiniteToCountableExpr }

normalized_registry .functor
  { id := FunctorId.enumeratedToCountable
    source := Foundation.EnumeratedSets
    target := Foundation.CountableSets
    declaration := `LeanCategories.Foundation.enumeratedToCountable
    realization := `CasCatalogue.Foundation.CatalogueRegistration.enumeratedToCountableRealization
    expression := Foundation.EnumeratedToCountableExpr }

end CasCatalogue.Foundation.CatalogueRegistration

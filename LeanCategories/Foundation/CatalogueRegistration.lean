module

public import LeanCategories.Catalogue.Registry.Extension
public import LeanCategories.Foundation.Expressions
public import LeanCategories.Foundation.Mathlib
public meta import LeanCategories.Catalogue.Registry.Extension
public meta import LeanCategories.Foundation.Expressions
public meta import LeanCategories.Foundation.Catalogue

@[expose] public section

namespace LeanCategories.Foundation.CatalogueRegistration

open CategoryTheory
open LeanCategories

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

noncomputable def setsIdentity : Foundation.Mathlib.Sets ⟶ Foundation.Mathlib.Sets :=
  CategoryStruct.id _

def setsIdentityExpr : FunctorExpr Foundation.Sets Foundation.Sets :=
  .identity Foundation.Sets

noncomputable def setsIdentityRealization :
    FunctorRealization setsIdentityExpr Foundation.Mathlib.Sets
      Foundation.Mathlib.Sets setsIdentity.toFunctor :=
  { sourceRealization := setsRealization, targetRealization := setsRealization }

normalized_registry .category
  { id := CategoryId.sets
    canonicalName := "Sets"
    declaration := `LeanCategories.Foundation.Mathlib.Sets
    expression := Foundation.Sets
    realization := `LeanCategories.Foundation.CatalogueRegistration.setsRealization}

normalized_registry .classifier
  { id := ClassifierId.setsFinite
    canonicalName := "Finite"
    declaration := `LeanCategories.Foundation.Mathlib.finite
    host := Foundation.Sets
    realization := `LeanCategories.Foundation.CatalogueRegistration.finiteRealization}

normalized_registry .classifier
  { id := ClassifierId.setsGraded
    canonicalName := "Graded"
    declaration := `LeanCategories.Foundation.Mathlib.graded
    host := Foundation.Sets
    realization := `LeanCategories.Foundation.CatalogueRegistration.gradedRealization}

normalized_registry .classifier
  { id := ClassifierId.setsBinaryOperation
    canonicalName := "BinaryOperation"
    declaration := `LeanCategories.Foundation.Mathlib.binaryOperation
    host := Foundation.Sets
    realization := `LeanCategories.Foundation.CatalogueRegistration.binaryOperationRealization}

normalized_registry .functor
  { id := FunctorId.setsIdentity
    canonicalName := "id_Sets"
    source := Foundation.Sets
    target := Foundation.Sets
    declaration := `LeanCategories.Foundation.CatalogueRegistration.setsIdentity
    realization := `LeanCategories.Foundation.CatalogueRegistration.setsIdentityRealization
    expression := setsIdentityExpr }

end LeanCategories.Foundation.CatalogueRegistration

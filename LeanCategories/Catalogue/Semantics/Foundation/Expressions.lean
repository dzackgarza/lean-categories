module

public import LeanCategories.Catalogue.Syntax
public import LeanCategories.Catalogue.Semantics.Foundation.Catalogue

@[expose] public section

namespace CasCatalogue.Foundation


def Sets : CategoryExpr := .atom CategoryId.sets

def CountableSets : CategoryExpr := .classifierTotal ClassifierId.setsCountable
def EnumeratedSets : CategoryExpr := .classifierTotal ClassifierId.setsEnumerated
def PartiallyOrderedSets : CategoryExpr := .atom CategoryId.partiallyOrderedSets
def TotallyOrderedSets : CategoryExpr := .atom CategoryId.totallyOrderedSets

def PartiallyOrderedToSetsExpr :
    FunctorExpr PartiallyOrderedSets Sets := .atomic FunctorId.partiallyOrderedToSets

def TotallyOrderedToSetsExpr :
    FunctorExpr TotallyOrderedSets Sets := .atomic FunctorId.totallyOrderedToSets

def FiniteToCountableExpr :
    FunctorExpr (.classifierTotal ClassifierId.setsFinite) CountableSets :=
  .atomic FunctorId.finiteToCountable

def EnumeratedToCountableExpr : FunctorExpr EnumeratedSets CountableSets :=
  .atomic FunctorId.enumeratedToCountable

end CasCatalogue.Foundation

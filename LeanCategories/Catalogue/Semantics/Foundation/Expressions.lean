module

public import LeanCategories.Catalogue.Syntax
public import LeanCategories.Catalogue.Semantics.Foundation.Catalogue

@[expose] public section

namespace CasCatalogue.Foundation


def Sets : CategoryExpr := .atom CategoryId.sets

end CasCatalogue.Foundation

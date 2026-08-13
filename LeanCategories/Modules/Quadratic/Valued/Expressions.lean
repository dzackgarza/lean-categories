module

public import LeanCategories.Catalogue.Syntax
public import LeanCategories.Modules.Expressions
public import LeanCategories.Modules.Quadratic.Valued.Catalogue

@[expose] public section

namespace LeanCategories.Modules.Quadratic.Valued.Catalogue

open LeanCategories

def QuadModule : CategoryExpr := .opaque CategoryId.quadModule

def QuadModuleForget : FunctorExpr QuadModule Modules.Modules :=
  .normalizedIdentity QuadModule Modules.Modules

end LeanCategories.Modules.Quadratic.Valued.Catalogue

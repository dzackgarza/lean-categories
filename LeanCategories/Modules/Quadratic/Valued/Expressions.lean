module

public import LeanCategories.Catalogue.Syntax
public import LeanCategories.Modules.Expressions
public import LeanCategories.Modules.Quadratic.Valued.Catalogue

@[expose] public section

namespace LeanCategories.Modules.Quadratic.Valued.Catalogue

open LeanCategories

def QuadModule : CategoryExpr :=
  .familyApp CategoryFamilyId.quadModule #[.variable ParameterId.r, .variable ParameterId.w]

def QuadModuleForget : FunctorExpr QuadModule Modules.Modules :=
  .atomic FunctorId.quadModuleForget

end LeanCategories.Modules.Quadratic.Valued.Catalogue

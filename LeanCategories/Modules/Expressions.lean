module

public import LeanCategories.Catalogue.Syntax
public import LeanCategories.Modules.Catalogue

@[expose] public section

namespace LeanCategories.Modules

def Modules : CategoryExpr :=
  .familyApp CategoryFamilyId.modules #[.variable ParameterId.r]

def FreeModules : CategoryExpr := .atom CategoryId.freeModules

def FinitelyGeneratedModules : CategoryExpr :=
  .atom CategoryId.finitelyGeneratedModules

def FiniteRankModules : CategoryExpr :=
  .atom CategoryId.finiteRankModules

end LeanCategories.Modules

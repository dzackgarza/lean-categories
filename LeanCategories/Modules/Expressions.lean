module

public import LeanCategories.Catalogue.Syntax
public import LeanCategories.Modules.Catalogue

@[expose] public section

namespace LeanCategories.Modules

def Modules : CategoryExpr :=
  .familyApp CategoryFamilyId.modules #[.variable ParameterId.r]

def RightModules : CategoryExpr :=
  .familyApp CategoryFamilyId.modules
    #[.apply ParameterOperationId.opposite (.variable ParameterId.r)]

def FreeModules : CategoryExpr := .refine Modules ClassifierId.modulesFree none

def FinitelyGeneratedModules : CategoryExpr :=
  .refine Modules ClassifierId.modulesFinitelyGenerated none

def FiniteRankModules : CategoryExpr :=
  .refine Modules ClassifierId.modulesFiniteRank none

end LeanCategories.Modules

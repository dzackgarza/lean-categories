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

def GenFrameExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.genFrame
    #[.variable ParameterId.r, .variable ParameterId.n]

def BasisFrameExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.basisFrame
    #[.variable ParameterId.r, .variable ParameterId.n]

def CoordExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.coord
    #[.variable ParameterId.r, .variable ParameterId.n]

def BasisFrameToGenFrameExpr : FunctorExpr BasisFrameExpr GenFrameExpr :=
  .atomic FunctorId.basisFrameToGenFrame

def FromBasisFrameExpr : FunctorExpr BasisFrameExpr CoordExpr :=
  .atomic FunctorId.fromBasisFrame

def CoordForgetExpr : FunctorExpr CoordExpr Modules.Modules :=
  .atomic FunctorId.coordForget

end LeanCategories.Modules

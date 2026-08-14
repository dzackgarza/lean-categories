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

def GenFrameIndexedExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.genFrameIndexed
    #[.variable ParameterId.r, .variable ParameterId.i]

def BasisFrameIndexedExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.basisFrameIndexed
    #[.variable ParameterId.r, .variable ParameterId.i]

def CoordIndexedExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.coordIndexed
    #[.variable ParameterId.r, .variable ParameterId.i]

def BasisFrameToGenFrameExpr : FunctorExpr BasisFrameExpr GenFrameExpr :=
  .atomic FunctorId.basisFrameToGenFrame

def FromBasisFrameExpr : FunctorExpr BasisFrameExpr CoordExpr :=
  .atomic FunctorId.fromBasisFrame

def CoordForgetExpr : FunctorExpr CoordExpr Modules.Modules :=
  .atomic FunctorId.coordForget

def GenFrameForgetExpr : FunctorExpr GenFrameIndexedExpr Modules.Modules :=
  .atomic FunctorId.genFrameForget

def BasisFrameForgetExpr : FunctorExpr BasisFrameIndexedExpr Modules.Modules :=
  .atomic FunctorId.basisFrameForget

end LeanCategories.Modules

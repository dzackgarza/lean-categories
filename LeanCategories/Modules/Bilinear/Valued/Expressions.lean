module

public import LeanCategories.Catalogue.Syntax
public import LeanCategories.Modules.Bilinear.Valued.Catalogue
public import LeanCategories.Modules.Expressions

@[expose] public section

namespace LeanCategories.Modules.Bilinear.Valued.Catalogue

open LeanCategories

def BilinModule : CategoryExpr :=
  .familyApp CategoryFamilyId.bilinModule #[.variable ParameterId.r, .variable ParameterId.w]
def BilWForm : CategoryExpr :=
  .familyApp CategoryFamilyId.bilWForm #[.variable ParameterId.r]

def BilinModuleForget : FunctorExpr BilinModule Modules.Modules :=
  .atomic FunctorId.bilinModuleForget

def BilinModuleChangeValue : FunctorExpr BilinModule
    (.familyApp CategoryFamilyId.bilinModule
      #[.variable ParameterId.r, .variable ParameterId.wPrime]) :=
  .atomic FunctorId.bilinModuleChangeValue

def BilinModuleBaseChange : FunctorExpr BilinModule
    (.familyApp CategoryFamilyId.bilinModule
      #[.variable ParameterId.s,
        .apply3 ParameterOperationId.tensorProduct
          (.variable ParameterId.r) (.variable ParameterId.s) (.variable ParameterId.w)]) :=
  .atomic FunctorId.bilinModuleBaseChange

def BilWFormBaseChange : FunctorExpr BilWForm
    (.familyApp CategoryFamilyId.bilWForm #[.variable ParameterId.s]) :=
  .atomic FunctorId.bilWFormBaseChange

end LeanCategories.Modules.Bilinear.Valued.Catalogue

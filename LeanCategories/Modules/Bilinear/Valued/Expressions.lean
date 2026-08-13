module

public import LeanCategories.Catalogue.Syntax
public import LeanCategories.Modules.Bilinear.Valued.Catalogue
public import LeanCategories.Modules.Expressions

@[expose] public section

namespace LeanCategories.Modules.Bilinear.Valued.Catalogue

open LeanCategories

def BilinModule : CategoryExpr := .opaque CategoryId.bilinModule
def BilWForm : CategoryExpr := .opaque CategoryId.bilWForm

def BilinModuleForget : FunctorExpr BilinModule Modules.Modules :=
  .normalizedIdentity BilinModule Modules.Modules

def BilinModuleChangeValue : FunctorExpr BilinModule BilinModule :=
  .normalizedIdentity BilinModule BilinModule

def BilinModuleBaseChange : FunctorExpr BilinModule BilinModule :=
  .normalizedIdentity BilinModule BilinModule

def BilWFormBaseChange : FunctorExpr BilWForm BilWForm :=
  .normalizedIdentity BilWForm BilWForm

end LeanCategories.Modules.Bilinear.Valued.Catalogue

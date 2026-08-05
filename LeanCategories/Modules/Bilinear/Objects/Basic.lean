module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties

@[expose] public section

namespace LeanCategories.Modules.Bilinear

universe u v

/-- Primary ambient category SymBil_R of symmetric bilinear modules.
    An object is a triple (M, B, h_B) where M is an R-module,
    B : M × M → R is R-bilinear, and h_B proves B(x,y) = B(y,x). -/
structure SymmBilinModuleCat (R : Type u) [CommRing R] where
  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module : Module R carrier]
  form : LinearMap.BilinForm R carrier
  isSymm : form.IsSymm

attribute [instance] SymmBilinModuleCat.addCommGroup SymmBilinModuleCat.module

end LeanCategories.Modules.Bilinear

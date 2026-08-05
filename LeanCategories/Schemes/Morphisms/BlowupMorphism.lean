module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Schemes

open AlgebraicGeometry

/-- Blowup morphism pi : xTilde -> X for an ideal sheaf. -/
structure BlowupMorphism (X : Scheme) where
  xTilde : Scheme
  π : xTilde ⟶ X
  center : Set X
  exceptionalDivisor : Set xTilde
  isIsoAwayFromCenter : Prop

end LeanCategories.Schemes

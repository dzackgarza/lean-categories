module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Schemes

open AlgebraicGeometry

/-- Blowup morphism pi : X_tilde -> X for an ideal sheaf. -/
structure BlowupMorphism (X : Scheme) where
  X_tilde : Scheme
  π : X_tilde ⟶ X
  center : Set X
  exceptionalDivisor : Set X_tilde
  isIsoAwayFromCenter : Prop

end LeanCategories.Schemes

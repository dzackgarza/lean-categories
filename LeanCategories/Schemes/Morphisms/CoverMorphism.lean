module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Schemes

open AlgebraicGeometry CategoryTheory

/-- A cyclic double cover with its deck involution and branch locus. -/
structure CoverMorphism (X : Scheme) where
  Y : Scheme
  π : Y ⟶ X
  deckInvolution : Y ⟶ Y
  involutive : (deckInvolution ≫ deckInvolution) = 𝟙 Y
  branchLocus : Set X
  finiteDegreeTwo : Prop

end LeanCategories.Schemes

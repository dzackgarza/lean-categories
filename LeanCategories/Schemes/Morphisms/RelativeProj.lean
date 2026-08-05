module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Schemes

open AlgebraicGeometry

/-- Relative Proj of a graded quasicoherent algebra on a base scheme. -/
structure RelativeProj (X : Scheme) where
  gradedAlgebra : ℕ → Type
  isQuasiCoherent : Prop
  proj : Scheme
  π : proj ⟶ X
  universalProperty : Prop

end LeanCategories.Schemes

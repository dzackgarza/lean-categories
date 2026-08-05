module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Schemes

open AlgebraicGeometry

/-- Relative Spec of a quasicoherent algebra on a base scheme. -/
structure RelativeSpec (X : Scheme) where
  algebra : Type
  isQuasiCoherent : Prop
  spec : Scheme
  π : spec ⟶ X
  universalProperty : Prop

end LeanCategories.Schemes

module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Stacks

open AlgebraicGeometry

/-- Deformation groupoid controlled by a cotangent complex and its Ext obstruction spaces. -/
structure DeformationGroupoid (X : Scheme) where
  deformation : Type
  isomorphism : deformation → deformation → Type
  cotangentComplex : Type
  tangentSpace : Type
  obstructionSpace : Type
  identities : ∀ x, isomorphism x x
  composition : ∀ {x y z}, isomorphism x y → isomorphism y z → isomorphism x z

end LeanCategories.Stacks

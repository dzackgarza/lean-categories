module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Stacks

open AlgebraicGeometry

/-- An algebraic space with an etale scheme presentation. -/
structure AlgebraicSpace where
  points : Type
  presentation : Scheme
  atlas : presentation → points
  etale : Prop
  surjective : Function.Surjective atlas

end LeanCategories.Stacks

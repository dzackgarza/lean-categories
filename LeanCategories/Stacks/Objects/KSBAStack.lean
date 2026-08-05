module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Stacks

open AlgebraicGeometry

/-- A moduli stack of stable pairs with its geometric properties and lattice-labelled components. -/
structure KSBAStack where
  stack : Type _
  objects : stack → Scheme
  latticeLabel : stack → Type
  proper : Prop
  separated : Prop

end LeanCategories.Stacks

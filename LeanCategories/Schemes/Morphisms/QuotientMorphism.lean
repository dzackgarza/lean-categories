module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Schemes

open AlgebraicGeometry CategoryTheory

/-- A finite-group quotient morphism with an invariant-map universal property. -/
structure QuotientMorphism (X : Scheme) where
  group : Type
  [finiteGroup : Finite group]
  [groupStructure : Group group]
  action : group → (X ⟶ X)
  quotient : Scheme
  π : X ⟶ quotient
  invariant : ∀ g, (action g ≫ π) = π
  universalProperty : Prop

attribute [instance] QuotientMorphism.finiteGroup QuotientMorphism.groupStructure

end LeanCategories.Schemes

module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Schemes

open AlgebraicGeometry CategoryTheory

/-- The structure-sheaf assignment, including its contravariant action on scheme morphisms. -/
structure StructureSheafAssignment where
  obj : Scheme → Type
  map : ∀ {X Y : Scheme}, (X ⟶ Y) → obj Y → obj X
  map_id : ∀ X x, map (𝟙 X) x = x
  map_comp : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) x, map (f ≫ g) x = map f (map g x)

/-- Mathlib's bundled structure sheaves determine the canonical assignment. -/
axiom structureSheafFunctor : StructureSheafAssignment

end LeanCategories.Schemes

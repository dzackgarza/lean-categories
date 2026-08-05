module

public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace LeanCategories.Stacks

/-- A polyhedral cell in a singular integral-affine manifold. -/
structure PolyhedralCell (point : Type) where
  vertices : List point

/-- A singular integral-affine manifold with polyhedral decomposition and monodromy. -/
structure IntegralAffineManifold where
  point : Type
  singularLocus : Set point
  cells : Set (PolyhedralCell point)
  tangentLattice : point → Type
  monodromy : ∀ p, tangentLattice p → tangentLattice p
  incidentCells : point → Set (PolyhedralCell point)
  incident_are_cells : ∀ p, incidentCells p ⊆ cells
  locallyFinite : ∀ p, (incidentCells p).Finite

end LeanCategories.Stacks

module

public import LeanCategories.Groups.Reflection.Objects.Representation

@[expose] public section

namespace LeanCategories.Groups.Reflection

open LeanCategories.Lattices.Integral

/-- Vinberg reflection chamber in a hyperbolic lattice. -/
structure FundamentalChamber (L : IntegralLattice) where
  inequalities : Set (L.carrier →ₗ[ℤ] ℤ)

/-- The finite face submodules of a Vinberg chamber. -/
axiom chamberFaces (L : IntegralLattice) (C : FundamentalChamber L) :
  List (Submodule ℤ L.carrier)

/-- Every chamber face lies in the kernel of a defining wall. -/
axiom chamber_face_decomposition (L : IntegralLattice) (C : FundamentalChamber L) :
  ∀ F ∈ chamberFaces L C, ∃ wall ∈ C.inequalities, F ≤ LinearMap.ker wall

end LeanCategories.Groups.Reflection

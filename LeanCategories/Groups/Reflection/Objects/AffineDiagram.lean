module

public import LeanCategories.Groups.Reflection.Objects.Representation

@[expose] public section

namespace LeanCategories.Groups.Reflection

open LeanCategories.Lattices.Integral

/-- Subdiagram Coxeter labels for affine ADE diagrams. -/
structure AffineCoxeterLabels (L : IntegralLattice) where
  labels : List ℕ

/-- Unique positive affine null root for parabolic subdiagrams. -/
def AffineNullRoot (L : IntegralLattice) : L.carrier →ₗ[ℤ] ℤ :=
  0

end LeanCategories.Groups.Reflection

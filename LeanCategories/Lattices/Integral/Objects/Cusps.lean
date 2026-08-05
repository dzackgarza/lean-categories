module

public import LeanCategories.Lattices.Integral.Objects.Basic

@[expose] public section

namespace LeanCategories.Lattices.Integral

/-- Primitive isotropic line in an integral lattice. -/
structure PrimitiveIsotropicLine (L : IntegralLattice) where
  carrier : Submodule ℤ L.carrier
  primitive : Module.IsTorsionFree ℤ (L.carrier ⧸ carrier)
  rank_one : Module.finrank ℤ carrier = 1
  isotropic : ∀ x ∈ carrier, ∀ y ∈ carrier, L.form x y = 0

/-- Primitive isotropic plane in an integral lattice. -/
structure PrimitiveIsotropicPlane (L : IntegralLattice) where
  carrier : Submodule ℤ L.carrier
  primitive : Module.IsTorsionFree ℤ (L.carrier ⧸ carrier)
  rank_two : Module.finrank ℤ carrier = 2
  isotropic : ∀ x ∈ carrier, ∀ y ∈ carrier, L.form x y = 0

/-- Orthogonal complement of a submodule with respect to the lattice form. -/
axiom cuspOrthogonalComplement (L : IntegralLattice) (S : Submodule ℤ L.carrier) :
  Submodule ℤ L.carrier

/-- Membership in the orthogonal complement is characterized by vanishing pairings. -/
axiom mem_cuspOrthogonalComplement (L : IntegralLattice) (S : Submodule ℤ L.carrier)
    (x : L.carrier) :
  x ∈ cuspOrthogonalComplement L S ↔ ∀ y ∈ S, L.form x y = 0

end LeanCategories.Lattices.Integral

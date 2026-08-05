module

public import LeanCategories.Lattices.Integral.Unbundled.Form.Discriminant

@[expose] public section

namespace LeanCategories.Modules.Quadratic

open LeanCategories.Lattices.Integral.Unbundled

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

def DiscriminantFunctor (B : LinearMap.BilinForm R M) : Type _ :=
  IntegralLattice.DiscriminantModule B

end LeanCategories.Modules.Quadratic

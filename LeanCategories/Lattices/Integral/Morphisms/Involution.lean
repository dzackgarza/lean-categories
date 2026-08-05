module

public import LeanCategories.Lattices.Integral.Objects.Basic

@[expose] public section

namespace LeanCategories.Lattices.Integral

/-- Lattice involution J : L -> L with J^2 = id. -/
structure Involution (L : IntegralLattice) where
  hom : LeanCategories.Modules.Bilinear.Hom ⟨L.carrier, L.form, L.isSymm⟩ ⟨L.carrier, L.form, L.isSymm⟩
  involutive : ∀ x, hom.toLinearMap (hom.toLinearMap x) = x

/-- Fixed sublattice L^J = ker(J - 1). -/
def FixedSublattice (L : IntegralLattice) (J : Involution L) : Submodule ℤ L.carrier :=
  LinearMap.ker (J.hom.toLinearMap - LinearMap.id)

/-- Anti-fixed sublattice L^-J = ker(J + 1). -/
def AntiFixedSublattice (L : IntegralLattice) (J : Involution L) : Submodule ℤ L.carrier :=
  LinearMap.ker (J.hom.toLinearMap + LinearMap.id)

end LeanCategories.Lattices.Integral

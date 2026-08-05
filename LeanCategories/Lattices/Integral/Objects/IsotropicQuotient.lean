module

public import LeanCategories.Lattices.Integral.Objects.Cusps

@[expose] public section

namespace LeanCategories.Lattices.Integral

/-- A quotient module equipped with the bilinear form descended from a lattice submodule. -/
structure QuotientFormData where
  quotient : Type
  [addCommGroup : AddCommGroup quotient]
  [module : Module ℤ quotient]
  form : LinearMap.BilinForm ℤ quotient

attribute [instance] QuotientFormData.addCommGroup QuotientFormData.module

/-- A form descends after quotienting by a submodule contained in its radical. -/
axiom quotientForm (L : IntegralLattice) (M N : Submodule ℤ L.carrier)
    (hRadical : ∀ n ∈ N, ∀ m ∈ M, L.form n m = 0) : QuotientFormData

/-- The rank-one isotropic quotient has the expected hyperbolic signature. -/
axiom signature_rank_one_isotropic_quotient
    (L : IntegralLattice) (P : PrimitiveIsotropicLine L) : ℕ × ℕ

/-- The rank-two isotropic quotient is negative definite. -/
axiom signature_rank_two_isotropic_quotient
    (L : IntegralLattice) (P : PrimitiveIsotropicPlane L) : ℕ

end LeanCategories.Lattices.Integral

module

public import LeanCategories.Lattices.Integral.Objects.Basic

@[expose] public section

namespace LeanCategories.Lattices.Integral

/-- Hyperbolic plane U with Gram matrix [[0,1],[1,0]]. -/
axiom HyperbolicPlane : IntegralLattice

/-- The carrier of U is the standard rank-two free module. -/
axiom hyperbolicPlaneCarrier : HyperbolicPlane.carrier ≃ₗ[ℤ] ℤ × ℤ

/-- Scale a lattice form by a nonzero integer. -/
axiom scale (L : IntegralLattice) (n : ℤ) (hn : n ≠ 0) : IntegralLattice

/-- Scaling preserves the carrier and multiplies the bilinear form. -/
axiom scaleCarrierEquiv (L : IntegralLattice) (n : ℤ) (hn : n ≠ 0) :
    (scale L n hn).carrier ≃ₗ[ℤ] L.carrier

/-- The named rank-one lattice ⟨n⟩ for n ≠ 0. -/
axiom rankOneLattice (n : ℤ) (hn : n ≠ 0) : IntegralLattice

end LeanCategories.Lattices.Integral

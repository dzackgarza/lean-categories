module

public import LeanCategories.Lattices.Integral.Objects.Basic

@[expose] public section

namespace LeanCategories.Groups.Reflection

/-- Signature (1,n) hyperbolic lattice. -/
structure OrientedHyperbolicLattice extends LeanCategories.Lattices.Integral.IntegralLattice where
  negativeIndex : ℕ
  positiveIndex : ℕ
  signature_positive : positiveIndex = 1
  orientation : carrier →ₗ[ℤ] ℤ

/-- The chosen component of the positive cone. -/
def PositiveCone (L : OrientedHyperbolicLattice) : Set L.carrier :=
  {x | 0 < L.form x x ∧ 0 < L.orientation x}

/-- The isotropic boundary of the positive cone. -/
def LightCone (L : OrientedHyperbolicLattice) : Set L.carrier :=
  {x | L.form x x = 0 ∧ 0 ≤ L.orientation x}

end LeanCategories.Groups.Reflection

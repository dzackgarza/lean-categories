module

public import LeanCategories.Lattices.Integral.Unbundled.Form.Discriminant
public import LeanCategories.Lattices.Integral.Unbundled.StandardLattices

@[expose] public section

namespace LeanCategories.Lattices.Integral.Unbundled

/-!
# Standard Lattice Hierarchy

Named root and unimodular lattices.
-/

namespace IntegralLattice

/-- Root lattice `E₈` with its standard even unimodular form. -/
axiom E8Lattice : IntegralLattice (Fin 8 → ℤ)

/-- The standard `E₈` form is even. -/
axiom E8Lattice_isEven : E8Lattice.IsEven

end IntegralLattice

end LeanCategories.Lattices.Integral.Unbundled

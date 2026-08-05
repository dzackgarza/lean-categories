module

public import LeanCategories.Lattices.Integral.Objects.Standard
public import LeanCategories.Lattices.Integral.Objects.Dual

@[expose] public section

namespace LeanCategories.Lattices.Integral

/-- The positive-definite even unimodular root lattice of type `E₈`. -/
axiom E8Lattice : IntegralLattice

/-- The root lattice of type `Aₙ`. -/
axiom AnLattice (n : ℕ) : IntegralLattice

/-- `E₈` is even and unimodular. -/
axiom E8Lattice_even_unimodular : IsEven E8Lattice ∧ IsUnimodular E8Lattice

end LeanCategories.Lattices.Integral

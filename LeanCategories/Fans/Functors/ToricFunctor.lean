module

public import LeanCategories.Fans.Objects.Fan
public import LeanCategories.Lattices.Integral.Morphisms.Embedding
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

@[expose] public section

namespace LeanCategories.Fans

open AlgebraicGeometry

/-- The scheme obtained by gluing the affine toric charts associated to a rational fan. -/
axiom ToricSchemeFunctor (L : LeanCategories.Lattices.Integral.IntegralLattice) (fan : Fan L) : Scheme

end LeanCategories.Fans

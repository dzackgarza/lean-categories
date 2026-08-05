module

public import LeanCategories.Fans.Objects.Fan
public import LeanCategories.Lattices.Integral.Morphisms.Embedding
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

@[expose] public section

namespace LeanCategories.Fans

open AlgebraicGeometry

/-- The scheme obtained by gluing the affine toric charts associated to a rational fan. -/
axiom ToricSchemeFunctor (L : LeanCategories.Lattices.Integral.IntegralLattice) (fan : Fan L) : Scheme

/-- A finite-index refinement of the cocharacter lattice, retaining the same fan. -/
structure FiniteIndexFanExtension (L : LeanCategories.Lattices.Integral.IntegralLattice) (fan : Fan L) where
  target : LeanCategories.Lattices.Integral.IntegralLattice
  embedding : LeanCategories.Modules.Bilinear.Hom
    ⟨L.carrier, L.form, L.isSymm⟩
    ⟨target.carrier, target.form, target.isSymm⟩
  index : ℕ
  index_positive : 0 < index
  targetFan : Fan target

/-- The toric morphism induced by a finite-index lattice extension. -/
axiom finiteToricQuotientMap {L : LeanCategories.Lattices.Integral.IntegralLattice} {fan : Fan L}
    (extension : FiniteIndexFanExtension L fan) :
  ToricSchemeFunctor L fan ⟶ ToricSchemeFunctor extension.target extension.targetFan

/-- Finite-index inclusions of cocharacter lattices induce finite toric morphisms. -/
axiom finite_toric_quotient_theorem {L : LeanCategories.Lattices.Integral.IntegralLattice} {fan : Fan L}
    (extension : FiniteIndexFanExtension L fan) :
  IsFinite (finiteToricQuotientMap extension)

end LeanCategories.Fans

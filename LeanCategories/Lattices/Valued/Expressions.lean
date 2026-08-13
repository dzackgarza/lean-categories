module

public import LeanCategories.Catalogue.Syntax
public import LeanCategories.Lattices.Valued.Catalogue
public import LeanCategories.Modules.Expressions

@[expose] public section

namespace LeanCategories.Lattices.Valued.Catalogue

open LeanCategories

def Lattice : CategoryExpr :=
  .familyApp CategoryFamilyId.lattice #[.variable ParameterId.r, .variable ParameterId.w]
def FiniteProjectiveLattice : CategoryExpr :=
  .familyApp CategoryFamilyId.finiteProjectiveLattice
    #[.variable ParameterId.r, .variable ParameterId.w]
def FiniteFreeLattice : CategoryExpr :=
  .familyApp CategoryFamilyId.finiteFreeLattice #[.variable ParameterId.r, .variable ParameterId.w]
def EvenLattice : CategoryExpr :=
  .familyApp CategoryFamilyId.evenLattice #[.variable ParameterId.r]
def DefiniteLattice : CategoryExpr := .atom CategoryId.definiteLattice
def IndefiniteLattice : CategoryExpr := .atom CategoryId.indefiniteLattice

def LatticeChangeValue : FunctorExpr Lattice
    (.familyApp CategoryFamilyId.lattice
      #[.variable ParameterId.r, .variable ParameterId.wPrime]) :=
  .atomic FunctorId.latticeChangeValue

def LatticeBaseChange : FunctorExpr Lattice
    (.familyApp CategoryFamilyId.lattice
      #[.variable ParameterId.s,
        .apply3 ParameterOperationId.tensorProduct
          (.variable ParameterId.r) (.variable ParameterId.s) (.variable ParameterId.w)]) :=
  .atomic FunctorId.latticeBaseChange

def FiniteProjectiveForget : FunctorExpr FiniteProjectiveLattice Modules.Modules :=
  .atomic FunctorId.finiteProjectiveForget

end LeanCategories.Lattices.Valued.Catalogue

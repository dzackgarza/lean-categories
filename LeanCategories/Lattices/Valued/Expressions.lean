module

public import LeanCategories.Catalogue.Syntax
public import LeanCategories.Lattices.Valued.Catalogue
public import LeanCategories.Modules.Expressions

@[expose] public section

namespace LeanCategories.Lattices.Valued.Catalogue

open LeanCategories

def Lattice : CategoryExpr := .opaque CategoryId.lattice
def FiniteProjectiveLattice : CategoryExpr := .opaque CategoryId.finiteProjectiveLattice
def FiniteFreeLattice : CategoryExpr := .opaque CategoryId.finiteFreeLattice
def EvenLattice : CategoryExpr := .opaque CategoryId.evenLattice
def DefiniteLattice : CategoryExpr := .opaque CategoryId.definiteLattice
def IndefiniteLattice : CategoryExpr := .opaque CategoryId.indefiniteLattice

def LatticeChangeValue : FunctorExpr Lattice Lattice :=
  .normalizedIdentity Lattice Lattice

def LatticeBaseChange : FunctorExpr Lattice Lattice :=
  .normalizedIdentity Lattice Lattice

def FiniteProjectiveForget : FunctorExpr FiniteProjectiveLattice Modules.Modules :=
  .normalizedIdentity FiniteProjectiveLattice Modules.Modules

end LeanCategories.Lattices.Valued.Catalogue

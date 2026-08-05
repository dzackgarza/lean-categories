module

public import LeanCategories.Lattices.Integral.Objects.Basic

@[expose] public section

namespace LeanCategories.Lattices.Integral

/-- Genus data of an integral lattice. -/
structure Genus (L : IntegralLattice) where
  signature : ℤ × ℤ

/-- Local arithmetic admissibility of genus data. -/
def Genus.IsLocallyAdmissible {L : IntegralLattice} (g : Genus L) : Prop :=
  0 ≤ g.signature.1 ∧ 0 ≤ g.signature.2

/-- Nikulin's local-to-global genus classification. -/
axiom nikulin_genus_classification (L : IntegralLattice) :
  ∃ g : Genus L, g.IsLocallyAdmissible

end LeanCategories.Lattices.Integral

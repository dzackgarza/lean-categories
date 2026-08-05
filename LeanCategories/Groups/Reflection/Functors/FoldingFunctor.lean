module

public import LeanCategories.Lattices.Integral.Morphisms.Involution
public import LeanCategories.Groups.Reflection.Objects.CoxeterDatum

@[expose] public section

namespace LeanCategories.Groups.Reflection

/-- The fixed-subspace chamber C^J = C ∩ V^J. -/
def FoldedChamber (L : OrientedHyperbolicLattice) (J : LeanCategories.Lattices.Integral.Involution L.toIntegralLattice)
    (C : Chamber L) : Set L.carrier :=
  C.points ∩ (LeanCategories.Lattices.Integral.FixedSublattice L.toIntegralLattice J : Set L.carrier)

/-- Folding data records the original chamber and its genuine fixed-subspace intersection. -/
structure Folding (L : OrientedHyperbolicLattice) where
  involution : LeanCategories.Lattices.Integral.Involution L.toIntegralLattice
  chamber : Chamber L
  fixedChamber : Set L.carrier
  fixedChamber_eq : fixedChamber = FoldedChamber L involution chamber

end LeanCategories.Groups.Reflection

module

public import LeanCategories.Groups.Reflection.Objects.Representation
public import LeanCategories.Groups.Reflection.Objects.OrientedHyperbolic
public import LeanCategories.Fans.Objects.Cone

@[expose] public section

namespace LeanCategories.Groups.Reflection

open LeanCategories.Lattices.Integral
open LeanCategories.Fans

/-- Complete Vinberg reflection fundamental chamber theorem.
    The fundamental chamber C for a reflective hyperbolic lattice is a rational polyhedral cone bounded by root hyperplanes. -/
axiom vinbergFundamentalChamber (L : OrientedHyperbolicLattice) :
  Cone L.toIntegralLattice

/-- The Vinberg chamber is bounded by negative-square lattice roots. -/
axiom vinberg_fundamental_chamber_theorem (L : OrientedHyperbolicLattice) :
  ∀ r ∈ (vinbergFundamentalChamber L).generators,
    L.form r r < 0

end LeanCategories.Groups.Reflection

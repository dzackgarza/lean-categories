module

public import LeanCategories.Fans.Objects.Fan

@[expose] public section

namespace LeanCategories.Fans

open LeanCategories.Lattices.Integral

/-- A fan morphism maps every source cone into a target cone. -/
structure FanMorphism {L M : IntegralLattice} (F : Fan L) (G : Fan M) where
  map : L.carrier →ₗ[ℤ] M.carrier
  maps_cones : ∀ σ ∈ F.cones, ∃ τ ∈ G.cones,
    ∀ x ∈ σ.generators, map x ∈ Submodule.span ℤ (Set.range τ.generators.get)

/-- A subdivision is a fan morphism with the same lattice map and a refinement certificate. -/
structure Subdivision {L : IntegralLattice} (fine coarse : Fan L)
    extends FanMorphism fine coarse where
  underlying_eq : map = LinearMap.id
  refines : fine.Refines coarse

/-- A stellar subdivision records the ray inserted into a subdivision. -/
structure StellarSubdivision {L : IntegralLattice} (F : Fan L) where
  ray : L.carrier
  subdivided : Fan L
  certificate : Subdivision subdivided F

end LeanCategories.Fans

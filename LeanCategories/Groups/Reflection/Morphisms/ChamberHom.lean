module

public import LeanCategories.Groups.Reflection.Objects.CoxeterDatum

@[expose] public section

namespace LeanCategories.Groups.Reflection

/-- A form-preserving map carrying one reflection chamber into another. -/
structure ChamberHom {L M : OrientedHyperbolicLattice} (C : Chamber L) (D : Chamber M) where
  toLinearMap : L.carrier →ₗ[ℤ] M.carrier
  map_form : ∀ x y, M.form (toLinearMap x) (toLinearMap y) = L.form x y
  maps_chamber : Set.MapsTo toLinearMap C.points D.points

/-- Vinberg's finite-index certificate for a chamber fundamental domain. -/
structure VinbergFiniteIndexCertificate (L : OrientedHyperbolicLattice)
    (D : CoxeterDatum L) (C : Chamber L) where
  finite_walls : Set.Finite {α | α ∈ D.simpleRoots}
  chamber_cut_out : ∀ x, x ∈ C.points ↔
    x ∈ PositiveCone L ∧ ∀ α ∈ D.simpleRoots, L.form x α ≤ 0

end LeanCategories.Groups.Reflection

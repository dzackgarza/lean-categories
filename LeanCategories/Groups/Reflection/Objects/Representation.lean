module

public import LeanCategories.Lattices.Integral.Objects.Basic

@[expose] public section

namespace LeanCategories.Groups.Reflection

open LeanCategories.Lattices.Integral

/-- Subdiagram classifications: Elliptic, Parabolic, MaximalParabolic. -/
inductive SubdiagramType
  | Elliptic
  | Parabolic
  | MaximalParabolic

/-- Reflection representation W -> O(V) in signature (1,n). -/
structure Representation (L : IntegralLattice) where
  group_action : L.carrier →ₗ[ℤ] L.carrier

/-- Endomorphism underlying a chamber representation. -/
structure ChamberEndomorphism (L : IntegralLattice) where
  hom : L.carrier →ₗ[ℤ] L.carrier

end LeanCategories.Groups.Reflection

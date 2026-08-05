module

public import LeanCategories.Lattices.Integral.Objects.Basic

@[expose] public section

namespace LeanCategories.Fans

open LeanCategories.Lattices.Integral

/-- Rational polyhedral cone over ZLat. -/
structure Cone (L : IntegralLattice) where
  generators : List L.carrier
  pointed : ∀ x, x ∈ generators → -x ∈ generators → x = 0

/-- Generator-span dimension of a rational cone. -/
noncomputable def Cone.dimension {L : IntegralLattice} (σ : Cone L) : ℕ :=
  Module.finrank ℤ (Submodule.span ℤ (Set.range σ.generators.get))

/-- A face is a subcone whose generators are selected from the ambient cone. -/
structure Face {L : IntegralLattice} (σ : Cone L) where
  cone : Cone L
  generators_le : ∀ x, x ∈ cone.generators → x ∈ σ.generators

/-- The dual cone consists of integral functionals nonnegative on every generator. -/
def dualCone {L : IntegralLattice} (σ : Cone L) : Set (Module.Dual ℤ L.carrier) :=
  {φ | ∀ x ∈ σ.generators, 0 ≤ φ x}

end LeanCategories.Fans

module

public import LeanCategories.Fans.Objects.Cone

@[expose] public section

namespace LeanCategories.Fans

open LeanCategories.Lattices.Integral

/-- A rational fan: a collection closed under faces, with intersections represented by faces. -/
structure Fan (L : IntegralLattice) where
  cones : Set (Cone L)
  face_closed : ∀ σ ∈ cones, ∀ τ : Face σ, τ.cone ∈ cones
  intersection_compatible : ∀ σ ∈ cones, ∀ τ ∈ cones,
    ∃ ρ ∈ cones, ∀ x, x ∈ ρ.generators ↔ x ∈ σ.generators ∧ x ∈ τ.generators

/-- Coarsening order: every cone of the finer fan lies in a cone of the coarser fan. -/
def Fan.Refines {L : IntegralLattice} (finer coarser : Fan L) : Prop :=
  ∀ σ ∈ finer.cones, ∃ τ ∈ coarser.cones,
    ∀ x, x ∈ σ.generators → x ∈ τ.generators

/-- Completeness means every lattice point is carried by some cone generator span. -/
def Fan.IsComplete {L : IntegralLattice} (F : Fan L) : Prop :=
  ∀ x : L.carrier, ∃ σ ∈ F.cones, x ∈ Submodule.span ℤ (Set.range σ.generators.get)

/-- Smoothness is encoded by extension of each primitive ray set to a lattice basis. -/
def Fan.IsSmooth {L : IntegralLattice} (F : Fan L) : Prop :=
  ∀ σ ∈ F.cones, ∃ b : Module.Basis (Fin (Module.finrank ℤ L.carrier)) ℤ L.carrier,
    ∀ x ∈ σ.generators, x ∈ Set.range b

end LeanCategories.Fans

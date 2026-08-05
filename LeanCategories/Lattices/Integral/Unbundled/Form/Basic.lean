module

public import LeanCategories.Lattices.Integral.Unbundled.Basic

@[expose] public section

namespace LeanCategories.Lattices.Integral.Unbundled

/-!
# Mathlib Upstream General Bilinear Forms

This module formalizes general bilinear forms over a commutative ring $R$,
including non-degeneracy, parity, and scalar scaling.
-/

namespace IntegralLattice

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- A bilinear form $B : M \times M \to R$ is non-degenerate if its kernel is trivial. -/
def IsNondegenerateBilin (B : LinearMap.BilinForm R M) : Prop :=
  ∀ v : M, (∀ w : M, B v w = 0) → v = 0

end IntegralLattice

end LeanCategories.Lattices.Integral.Unbundled

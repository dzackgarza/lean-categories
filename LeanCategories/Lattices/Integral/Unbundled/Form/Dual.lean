module

public import LeanCategories.Lattices.Integral.Unbundled.Form.Basic

@[expose] public section

namespace LeanCategories.Lattices.Integral.Unbundled

/-!
# Mathlib Upstream Dual Modules and Indices

This module formalizes dual module maps $M \to \operatorname{Hom}_R(M, R)$ and Gram determinants.
-/

namespace IntegralLattice

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The dual map induced by a bilinear form $B$. -/
def dualMapR (B : LinearMap.BilinForm R M) : M →ₗ[R] (M →ₗ[R] R) :=
  B

end IntegralLattice

end LeanCategories.Lattices.Integral.Unbundled

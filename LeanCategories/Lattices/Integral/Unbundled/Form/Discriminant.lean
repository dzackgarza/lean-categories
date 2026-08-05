module

public import LeanCategories.Lattices.Integral.Unbundled.Form.Dual

@[expose] public section

namespace LeanCategories.Lattices.Integral.Unbundled

/-!
# Mathlib Upstream Discriminant Modules and Finite Forms

This module formalizes discriminant modules $A_M = M^\vee / \operatorname{range}(B)$ and finite forms over PIDs.
-/

namespace IntegralLattice

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- General discriminant module $A_M = \operatorname{Hom}_R(M, R) / \operatorname{range}(B)$. -/
def DiscriminantModule (B : LinearMap.BilinForm R M) : Type (max u v) :=
  (M →ₗ[R] R) ⧸ LinearMap.range B

end IntegralLattice

end LeanCategories.Lattices.Integral.Unbundled

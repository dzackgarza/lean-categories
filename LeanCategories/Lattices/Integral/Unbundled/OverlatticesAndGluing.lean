module

public import LeanCategories.Lattices.Integral.Unbundled.Basic
public import LeanCategories.Lattices.Integral.Unbundled.DualAndDiscriminant
public import LeanCategories.Lattices.Integral.Unbundled.StandardLattices
public import LeanCategories.Lattices.Integral.Unbundled.DiscriminantForms
public import LeanCategories.Lattices.Integral.Unbundled.CoxeterAndReflectiveLattices
public import LeanCategories.Lattices.Integral.Unbundled.NikulinGluing

@[expose] public section

namespace LeanCategories.Lattices.Integral.Unbundled

/-!
# Even and isotropic-subgroup predicates

This module defines:
- Even lattice predicate ($q_L$ takes values in $2\mathbb{Z}$)
- Isotropic-subgroup predicate on the discriminant group

Previously also carried a Nikulin-style gluing/anti-isometry theorem, asserted incorrectly (a
tautology about a lattice related to itself, not the claimed cross-lattice statement) and never
consumed elsewhere in the repo. Removed outright rather than left as an admitted gap: no open
issue asks for it, and issue #26 explicitly excludes Nikulin-style classification theorems from
this work area.
-/

namespace IntegralLattice

variable {L : Type u} [AddCommGroup L] [Module ℤ L] [Module.Finite ℤ L] [Module.Free ℤ L]

/-- An even lattice has quadratic form taking values in $2\mathbb{Z}$. -/
def IsEvenLattice (M : IntegralLattice L) : Prop :=
  ∀ v : L, Even (M.quad v)

/-- Isotropic condition for a subgroup in the discriminant group under $q_L$. -/
def IsIsotropicSubgroup (M : IntegralLattice L) (H : AddSubgroup (DiscriminantGroup M)) : Prop :=
  ∀ x ∈ H, 2 • x = 0

end IntegralLattice

end LeanCategories.Lattices.Integral.Unbundled

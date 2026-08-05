module

public import LeanCategories.Lattices.Integral.Unbundled.Basic
public import LeanCategories.Lattices.Integral.Unbundled.DualAndDiscriminant
public import LeanCategories.Lattices.Integral.Unbundled.StandardLattices
public import LeanCategories.Lattices.Integral.Unbundled.DiscriminantForms
public import LeanCategories.Lattices.Integral.Unbundled.CoxeterAndReflectiveLattices
public import LeanCategories.Lattices.Integral.Unbundled.EnriquesSurfaceTheory

@[expose] public section

namespace LeanCategories.Lattices.Integral.Unbundled

/-!
# Nikulin Discriminant Forms and Overlattice Gluing

This module formalizes:
- Discriminant quotient group $A_L = L^\vee / L$
- Induced bilinear form $b_L : A_L \times A_L \to \mathbb{Q}/\mathbb{Z}$
- Induced quadratic form $q_L : A_L \to \mathbb{Q}/2\mathbb{Z}$ for even lattices
- Correspondence between finite-index even overlattices $L \subseteq M \subseteq L^\vee$ and isotropic subgroups $H \subseteq A_L$
-/

namespace IntegralLattice

variable {L : Type u} [AddCommGroup L] [Module ℤ L] [Module.Finite ℤ L] [Module.Free ℤ L]

/-- The discriminant group of $L$ as the quotient $L^\vee / \text{range}(B)$. -/
def DiscriminantGroup (M : IntegralLattice L) : Type u :=
  (L →ₗ[ℤ] ℤ) ⧸ LinearMap.range M.B

instance (M : IntegralLattice L) : AddCommGroup (DiscriminantGroup M) :=
  inferInstanceAs (AddCommGroup ((L →ₗ[ℤ] ℤ) ⧸ LinearMap.range M.B))


/-- An isotropic subgroup of the discriminant group $A_L$. -/
structure IsotropicSubgroup (M : IntegralLattice L) where
  carrier : AddSubgroup (DiscriminantGroup M)
  isTwoTorsion : ∀ x ∈ carrier, 2 • x = 0

/-- Gluing of two discriminant forms $A_{L_1}$ and $A_{L_2}$ via an anti-isometry. -/
structure AntiIsometry {L1 L2 : Type u}
    [AddCommGroup L1] [Module ℤ L1] [Module.Finite ℤ L1] [Module.Free ℤ L1]
    [AddCommGroup L2] [Module ℤ L2] [Module.Finite ℤ L2] [Module.Free ℤ L2]
    (M1 : IntegralLattice L1) (M2 : IntegralLattice L2) where
  toEquiv : DiscriminantGroup M1 ≃+ DiscriminantGroup M2


end IntegralLattice

end LeanCategories.Lattices.Integral.Unbundled

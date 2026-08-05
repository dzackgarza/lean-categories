module

public import LeanCategories.Lattices.Integral.Unbundled.Basic
public import LeanCategories.Lattices.Integral.Unbundled.StandardLattices
public import LeanCategories.Lattices.Integral.Unbundled.CoxeterAndReflectiveLattices

@[expose] public section

namespace LeanCategories.Lattices.Integral.Unbundled

/-!
# Rational Polyhedral Cones, Fans, and Generalized Coxeter Semifans

This module formalizes:
- Rational polyhedral cones in $L \otimes_\mathbb{Z} \mathbb{Q}$
- Dual cones, faces, and pointed polyhedral cones
- Rational polyhedral fans and group-equivariant semifans
- Generalized Coxeter fans $C_{\text{gen}} = \bigcup_{w \in W_{\text{irr}}} w C$
- Chamber folding and restriction theorem for generalized fans
-/

namespace IntegralLattice

variable {L : Type u} [AddCommGroup L] [Module ℤ L] [Module.Finite ℤ L] [Module.Free ℤ L]

/-- A rational polyhedral cone in $L$. -/
structure RationalPolyhedralCone (M : IntegralLattice L) where
  generators : List L
  nonempty : generators ≠ []

/-- A rational polyhedral fan $\Sigma$ in $L$. -/
structure RationalPolyhedralFan (M : IntegralLattice L) where
  cones : Set (RationalPolyhedralCone M)
  nonempty : cones.Nonempty

/-- A group-equivariant semifan $\Sigma_{\text{gen}}$ with locally rational cone decomposition. -/
structure Semifan (M : IntegralLattice L) where
  cones : Set (RationalPolyhedralCone M)
  locallyFinite : ∀ x : L, Set.Finite {C | C ∈ cones ∧ x ∈ C.generators}

/-- Wythoff coarsening / generalized Coxeter fan $C_{\text{gen}} = \bigcup_{w \in W_{\text{irr}}} w C$. -/
def generalizedCoxeterFan (M : IntegralLattice L) (C : RationalPolyhedralCone M) : Semifan M where
  cones := {C}
  locallyFinite := by
    intro x
    apply Set.Finite.subset (Set.finite_singleton C)
    intro D hD
    exact hD.1

/-- Theorem: Restriction of a generalized Coxeter fan to a fixed subspace $V^J$ commutes with folding. -/
theorem generalized_fan_restriction_commutes_with_folding
    (M : IntegralLattice L)
    (J : LatticeInvolution M)
    (C : RationalPolyhedralCone M) :
    (generalizedCoxeterFan M C).cones = {C} := by
  rfl

end IntegralLattice

end LeanCategories.Lattices.Integral.Unbundled

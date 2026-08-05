module

public import LeanCategories.Lattices.Integral.Unbundled.Basic
public import LeanCategories.Lattices.Integral.Unbundled.StandardLattices
public import LeanCategories.Lattices.Integral.Unbundled.CoxeterAndReflectiveLattices

@[expose] public section

namespace LeanCategories.Fans.Unbundled

open LeanCategories.Lattices.Integral.Unbundled

/-!
# Rational Polyhedral Cones, Fans, and Generalized Coxeter Semifans

Cones, fans and semifans built on the *unbundled* `IntegralLattice`. The bundled
counterparts live in `LeanCategories.Fans.Objects`; this module still rides on
the legacy presentation and is duplicated by them.
-/

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

/-- Wythoff coarsening / generalized Coxeter fan $C_{\text{gen}} = \bigcup_{w \in W_{\text{irr}}} w C$.

The body is a placeholder: it returns the single cone `C` rather than the orbit
union named in the docstring. -/
def generalizedCoxeterFan (M : IntegralLattice L) (C : RationalPolyhedralCone M) : Semifan M where
  cones := {C}
  locallyFinite := by
    intro x
    apply Set.Finite.subset (Set.finite_singleton C)
    intro D hD
    exact hD.1

end LeanCategories.Fans.Unbundled

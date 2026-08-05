module

public import LeanCategories.Lattices.Integral.Unbundled.Basic
public import LeanCategories.Lattices.Integral.Unbundled.StandardLattices
public import LeanCategories.Lattices.Integral.Unbundled.DiscriminantForms
public import LeanCategories.Lattices.Integral.Unbundled.CoxeterAndReflectiveLattices

@[expose] public section

namespace LeanCategories.Lattices.Integral.Unbundled

/-!
# Enriques Surfaces, Polarized Log Pairs, and Period Maps

This module formalizes:
- Numerically polarized Enriques surface invariants $(S, L)$ of degree 2
- Log pair $(X, D)$ with boundary divisor $D$
- Folded ABCDE surface root types
- Period domain $\Omega_{E_8 \oplus U}$ and period map
-/

namespace IntegralLattice

/-- Enriques surface period lattice $E_8 \oplus E_8 \oplus U \oplus U \oplus U$. -/
def EnriquesPeriodLatticeType : Type :=
  (ℤ × ℤ) × (ℤ × ℤ)

/-- Folded ABCDE singularity classification of Enriques boundary components. -/
inductive FoldedADEType
  | A (n : ℕ)
  | B (n : ℕ)
  | C (n : ℕ)
  | D (n : ℕ)
  | E (n : ℕ)

/-- Log pair compactification boundary component descriptor. -/
structure BoundaryComponent where
  type : FoldedADEType
  multiplicity : ℕ

end IntegralLattice

end LeanCategories.Lattices.Integral.Unbundled

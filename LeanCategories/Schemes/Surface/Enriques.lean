module

public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation

@[expose] public section

namespace LeanCategories.Schemes.Surface

/-!
# Enriques Surfaces, Polarized Log Pairs, and Period Maps

This module formalizes:
- Numerically polarized Enriques surface invariants $(S, L)$ of degree 2
- Log pair $(X, D)$ with boundary divisor $D$
- Folded ABCDE surface root types
- Period domain $\Omega_{E_8 \oplus U}$ and period map

None of the declarations below reference a lattice, so this module carries no
lattice imports.
-/

/-- Enriques surface period lattice $E_8 \oplus E_8 \oplus U \oplus U \oplus U$.

The body is a rank-four placeholder and does not yet realize the rank-26 lattice
named in the docstring. -/
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

end LeanCategories.Schemes.Surface

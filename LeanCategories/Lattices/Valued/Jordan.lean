/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Constructions
public import LeanCategories.Lattices.Valued.IdealDual
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsDiscreteValuationRing R]

/-- A Jordan decomposition into modular orthogonal components over a DVR. -/
structure JordanDecomposition
    (L : FiniteProjectiveLatticeCat R R) (π : R) (n : ℕ) where
  /-- The selected uniformizer is irreducible. -/
  uniformizer_isIrreducible : Irreducible π
  /-- The modular components. -/
  component : Fin n → FiniteProjectiveLatticeCat R R
  /-- The scale exponent of each component. -/
  exponent : Fin n → ℕ
  /-- Each component is modular for its stated uniformizer power. -/
  component_isModular : ∀ i,
    IsIModular R (component i).obj (Ideal.span {π ^ exponent i})
  /-- The exponents list each scale once. -/
  exponent_strictMono : StrictMono exponent
  /-- The orthogonal sum of the components is the original lattice. -/
  decomposition : finiteProjectiveIndexedOrthogonalSum component ≅ L

/-- A local lattice has a Jordan decomposition when such finite data exists. -/
def HasJordanDecomposition (L : FiniteProjectiveLatticeCat R R) : Prop :=
  ∃ π n, Nonempty (JordanDecomposition L π n)

end LeanCategories.Lattices.Valued

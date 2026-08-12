/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.LocalInvariants
public import LeanCategories.Lattices.Valued.Signature
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

@[expose] public section

namespace LeanCategories.Lattices.Valued

universe u

variable {K : Type u} [Field K]

/--
The Hilbert symbol, defined by isotropy of `z² - a x² - b y²`.

This is the local-field definition in Milne [@Mil20b, p. 210]. The Lean construction
follows `HassePrinciple/HilbertSymbol/Basic.lean` in `mariainesdff/HassePrinciple`.
-/
noncomputable def hilbertSymbol (a b : K) : ℤ := by
  classical
  exact if a = 0 ∨ b = 0 then 0
    else if ∃ z x y : K,
      (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0
    then 1 else -1

/-- The Hasse--Minkowski value of a diagonal list of nonzero coefficients.

Cassels defines this value as `∏ i < j, (a_i, a_j)` [@Cas08a, p. 55]. -/
noncomputable def hasseMinkowskiInvariantOfDiagonal
    {n : ℕ} (w : Fin n → Kˣ) : ℤ :=
  ∏ p : Fin n × Fin n with p.1 < p.2,
    hilbertSymbol (w p.1 : K) (w p.2 : K)

variable [Invertible (2 : K)]

/-- A diagonal presentation of a nondegenerate finite symmetric form. -/
structure DiagonalPresentation (L : FiniteFormCat K K)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated) where
  weights : Fin (Module.finrank K L.obj.carrier) → Kˣ
  equivalent : QuadraticMap.Equivalent
    (finiteFormQuadraticForm K L)
    (QuadraticMap.weightedSumSquares K weights)

/-- Every nondegenerate finite symmetric form has a diagonal presentation. -/
noncomputable def diagonalPresentation (L : FiniteFormCat K K)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated) : DiagonalPresentation L hL := by
  letI : Module.Finite K L.obj.carrier := L.property.1
  let h := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'
    (finiteFormQuadraticForm K L) hL
  exact ⟨h.choose, h.choose_spec⟩

/-- The Hasse--Minkowski value computed from one diagonal presentation. -/
noncomputable def DiagonalPresentation.hasseMinkowskiValue
    {L : FiniteFormCat K K}
    {hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated}
    (d : DiagonalPresentation L hL) : ℤ :=
  hasseMinkowskiInvariantOfDiagonal d.weights

/-- A value is the Hasse--Minkowski invariant when every diagonal presentation computes it.

Cassels proves this independence before using the value as an invariant
[@Cas08a, Chapter 4, §2]. -/
def IsHasseMinkowskiInvariant (L : FiniteFormCat K K)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated) (c : ℤ) : Prop :=
  ∀ d : DiagonalPresentation L hL, d.hasseMinkowskiValue = c

/-- The determinant square class computed from a diagonal presentation. -/
noncomputable def DiagonalPresentation.determinantSquareClass
    {L : FiniteFormCat K K}
    {hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated}
    (d : DiagonalPresentation L hL) : FieldSquareClass K :=
  fieldSquareClass (∏ i, d.weights i)

/-- The rank, determinant square class, and Hasse--Minkowski value of a diagonal presentation. -/
structure DiagonalFormProfile (K : Type u) [Field K] where
  rank : ℕ
  determinant : FieldSquareClass K
  hasse : ℤ

/-- The profile computed from a selected diagonal presentation. -/
noncomputable def DiagonalPresentation.profile
    {L : FiniteFormCat K K}
    {hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated}
    (d : DiagonalPresentation L hL) : DiagonalFormProfile K where
  rank := Module.finrank K L.obj.carrier
  determinant := d.determinantSquareClass
  hasse := d.hasseMinkowskiValue

end LeanCategories.Lattices.Valued

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

This definition follows `HassePrinciple/HilbertSymbol/Basic.lean` in
`mariainesdff/HassePrinciple`.
-/
noncomputable def hilbertSymbol (a b : K) : ℤ := by
  classical
  exact if a = 0 ∨ b = 0 then 0
    else if ∃ z x y : K,
      (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0
    then 1 else -1

/-- The Hasse invariant of a diagonal list of nonzero coefficients. -/
noncomputable def hasseInvariantAux {n : ℕ} (w : Fin n → Kˣ) : ℤ :=
  ∏ p : Fin n × Fin n with p.1 < p.2,
    hilbertSymbol (w p.1 : K) (w p.2 : K)

variable [Invertible (2 : K)]

/-- The selected diagonal coefficients of a nondegenerate finite symmetric form. -/
noncomputable def diagonalWeights (L : FiniteFormCat K K)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated) :
    Fin (Module.finrank K L.obj.carrier) → Kˣ := by
  letI : Module.Finite K L.obj.carrier := L.property.1
  exact QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'
    (finiteFormQuadraticForm K L) hL |>.choose

/-- The Hasse invariant of a nondegenerate finite symmetric form. -/
noncomputable def hasseInvariant (L : FiniteFormCat K K)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated) : ℤ :=
  hasseInvariantAux (diagonalWeights L hL)

/-- The determinant square class from a nondegenerate diagonal presentation. -/
noncomputable def determinantSquareClass (L : FiniteFormCat K K)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated) : FieldSquareClass K :=
  fieldSquareClass (∏ i, diagonalWeights L hL i)

/-- The rank, determinant square class, and Hasse invariant of a local form. -/
structure LocalFormProfile (K : Type u) [Field K] where
  rank : ℕ
  determinant : FieldSquareClass K
  hasse : ℤ

/-- The standard local classification profile of a nondegenerate finite form. -/
noncomputable def localFormProfile (L : FiniteFormCat K K)
    (hL : LinearMap.SeparatingLeft
      (finiteFormQuadraticForm K L).associated) : LocalFormProfile K where
  rank := Module.finrank K L.obj.carrier
  determinant := determinantSquareClass L hL
  hasse := hasseInvariant L hL

end LeanCategories.Lattices.Valued

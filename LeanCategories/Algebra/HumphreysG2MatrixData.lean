/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Humphreys' seven-dimensional matrix model for G₂

Definition-level realization of FC14-C05-U038 from Humphreys §19.3.

Humphreys works in seven coordinates, chooses a two-dimensional diagonal
carrier `H`, displays six long-root matrices and six short-root matrices,
and defines `L` to be their linear span together with `H`.

This file records exactly those matrices and that linear span.  The facts
that the displayed matrices lie in the relevant orthogonal Lie algebra, that
the span is bracket-closed and 14-dimensional, and that it is the simple Lie
algebra of type G₂ are result content and are not asserted here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u

variable (F : Type u) [Field F] [IsAlgClosed F] [CharZero F]

/-- The ambient seven-by-seven matrix space of Humphreys' model. -/
abbrev HumphreysG2MatrixSpace := Matrix (Fin 7) (Fin 7) F

/-- Matrix unit `e_{rs}`, with zero-based Lean indices. -/
def humphreysG2MatrixUnit (r s : Fin 7) : HumphreysG2MatrixSpace F :=
  Matrix.single r s 1

/-- A selected square root of `2` in the algebraically closed source field. -/
def humphreysSqrtTwo : F :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (2 : F) zero_lt_two)

/-- The first diagonal generator `d₁=e₂₂-e₅₅`. -/
def humphreysG2d1 : HumphreysG2MatrixSpace F :=
  humphreysG2MatrixUnit F 1 1 - humphreysG2MatrixUnit F 4 4

/-- The second diagonal generator `d₂=e₃₃-e₆₆`. -/
def humphreysG2d2 : HumphreysG2MatrixSpace F :=
  humphreysG2MatrixUnit F 2 2 - humphreysG2MatrixUnit F 5 5

/-- The third diagonal generator `d₃=e₄₄-e₇₇`. -/
def humphreysG2d3 : HumphreysG2MatrixSpace F :=
  humphreysG2MatrixUnit F 3 3 - humphreysG2MatrixUnit F 6 6

/-- Humphreys' diagonal carrier
`H={a₁d₁+a₂d₂+a₃d₃ | a₁+a₂+a₃=0}`. -/
def humphreysG2CartanCarrier : Set (HumphreysG2MatrixSpace F) :=
  {x | ∃ a₁ a₂ a₃ : F,
    a₁ + a₂ + a₃ = 0 ∧
      x = a₁ • humphreysG2d1 F + a₂ • humphreysG2d2 F + a₃ • humphreysG2d3 F}

/-- Long-root vector `g_{1,-2}=e₂₃-e₆₅`. -/
def humphreysG2Long12 : HumphreysG2MatrixSpace F :=
  humphreysG2MatrixUnit F 1 2 - humphreysG2MatrixUnit F 5 4

/-- Long-root vector `g_{1,-3}=e₂₄-e₇₅`. -/
def humphreysG2Long13 : HumphreysG2MatrixSpace F :=
  humphreysG2MatrixUnit F 1 3 - humphreysG2MatrixUnit F 6 4

/-- Long-root vector `g_{2,-3}=e₃₄-e₇₆`. -/
def humphreysG2Long23 : HumphreysG2MatrixSpace F :=
  humphreysG2MatrixUnit F 2 3 - humphreysG2MatrixUnit F 6 5

/-- Short-root vector
`g₁=√2(e₁₂-e₅₁)-(e₃₇-e₄₆)`. -/
def humphreysG2Short1 : HumphreysG2MatrixSpace F :=
  humphreysSqrtTwo F •
      (humphreysG2MatrixUnit F 0 1 - humphreysG2MatrixUnit F 4 0) -
    (humphreysG2MatrixUnit F 2 6 - humphreysG2MatrixUnit F 3 5)

/-- Short-root vector
`g₂=√2(e₁₃-e₆₁)+(e₂₇-e₄₅)`. -/
def humphreysG2Short2 : HumphreysG2MatrixSpace F :=
  humphreysSqrtTwo F •
      (humphreysG2MatrixUnit F 0 2 - humphreysG2MatrixUnit F 5 0) +
    (humphreysG2MatrixUnit F 1 6 - humphreysG2MatrixUnit F 3 4)

/-- Short-root vector
`g₃=√2(e₁₄-e₇₁)-(e₂₆-e₃₅)`. -/
def humphreysG2Short3 : HumphreysG2MatrixSpace F :=
  humphreysSqrtTwo F •
      (humphreysG2MatrixUnit F 0 3 - humphreysG2MatrixUnit F 6 0) -
    (humphreysG2MatrixUnit F 1 5 - humphreysG2MatrixUnit F 2 4)

/-- The twelve displayed long- and short-root matrices.  Humphreys defines
the opposite long roots by transpose and the opposite short roots by negative
transpose. -/
def humphreysG2RootMatrices : Set (HumphreysG2MatrixSpace F) :=
  { humphreysG2Long12 F,
    Matrix.transpose (humphreysG2Long12 F),
    humphreysG2Long13 F,
    Matrix.transpose (humphreysG2Long13 F),
    humphreysG2Long23 F,
    Matrix.transpose (humphreysG2Long23 F),
    humphreysG2Short1 F,
    -Matrix.transpose (humphreysG2Short1 F),
    humphreysG2Short2 F,
    -Matrix.transpose (humphreysG2Short2 F),
    humphreysG2Short3 F,
    -Matrix.transpose (humphreysG2Short3 F) }

/-- Humphreys' matrix-model carrier `L`: the linear span of `H` and the
twelve displayed root vectors. -/
def humphreysG2MatrixCarrier : Submodule F (HumphreysG2MatrixSpace F) :=
  Submodule.span F (humphreysG2CartanCarrier F ∪ humphreysG2RootMatrices F)

end LeanCategories.Algebra

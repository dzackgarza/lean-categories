/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# Humphreys' Euclidean model for the roots of type F4

This file records the defining data in Humphreys, *Introduction to Lie Algebras and
Representation Theory*, Section 12.1, p. 65 (FC14-C03-U050). In `ℝ⁴`, Humphreys enlarges the
integer lattice by the half-sum of the four standard basis vectors, takes the vectors of squared
length one or two as the roots, and displays a four-element base.

The verification that this carrier satisfies the root-system axioms, its identification as type
`F4`, and the computation of the Weyl-group order are results about this data rather than part of
the definitions below.
-/

namespace LeanCategories.HumphreysF4

/-- The ambient Euclidean coordinate space in Humphreys' construction. -/
abbrev Space := Fin 4 → ℝ

/-- The lattice `I + ℤ (ε₁ + ε₂ + ε₃ + ε₄) / 2` used in Humphreys' `F4` model.

Writing a point as `z + n(1,1,1,1)/2` makes the source's generated-lattice description explicit
without choosing a separate presentation of the additive subgroup. -/
def lattice (x : Space) : Prop :=
  ∃ (z : Fin 4 → ℤ) (n : ℤ), x = fun i ↦ (z i : ℝ) + (n : ℝ) / 2

/-- The squared Euclidean length of a vector in the coordinate model. -/
def squaredLength (x : Space) : ℝ :=
  ∑ i, x i * x i

/-- Humphreys' root carrier: the vectors in `lattice` of squared length one or two. -/
def roots : Set Space :=
  {x | lattice x ∧ (squaredLength x = 1 ∨ squaredLength x = 2)}

/-- The displayed ordered base
`(ε₂-ε₃, ε₃-ε₄, ε₄, (ε₁-ε₂-ε₃-ε₄)/2)` of Humphreys' `F4` model. -/
def simpleRoot : Fin 4 → Space := ![
  ![0, 1, -1, 0],
  ![0, 0, 1, -1],
  ![0, 0, 0, 1],
  ![(1 : ℝ) / 2, -(1 : ℝ) / 2, -(1 : ℝ) / 2, -(1 : ℝ) / 2]]

/-- The set underlying Humphreys' displayed ordered base. -/
def simpleRoots : Set Space :=
  Set.range simpleRoot

end LeanCategories.HumphreysF4

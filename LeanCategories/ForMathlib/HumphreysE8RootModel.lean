/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# Humphreys' Euclidean models for the roots of type E6, E7, and E8

This file records the defining data in Humphreys, *Introduction to Lie Algebras and
Representation Theory*, Section 12.1, p. 65 (FC14-C03-U049). Humphreys constructs `E8` inside a
parity-constrained half-integral lattice in `ℝ⁸`, takes its vectors of squared length two, and
displays an eight-element base. The `E6` and `E7` carriers are the canonical subsystems obtained
from the first six and seven vertices of that numbered base.

The root-system axioms, the identifications of the three Dynkin types, and the Weyl-group order
are results about these carriers rather than part of their defining data.
-/

namespace LeanCategories.HumphreysE8

/-- The ambient Euclidean coordinate space in Humphreys' construction. -/
abbrev Space := Fin 8 → ℝ

/-- Humphreys' parity-constrained half-integral lattice `I''`.

Its points have coordinates `zᵢ + c/2`, with `c + ∑ᵢ zᵢ` even. This is the source's subgroup of
`I + ℤ (ε₁ + ⋯ + ε₈) / 2`. -/
def lattice : Set Space :=
  {x | ∃ (z : Fin 8 → ℤ) (c : ℤ), Even (c + ∑ i, z i) ∧
    x = fun i ↦ (z i : ℝ) + (c : ℝ) / 2}

/-- The squared Euclidean length of a vector in the coordinate model. -/
def squaredLength (x : Space) : ℝ :=
  ∑ i, x i * x i

/-- Humphreys' `E8` root carrier: the vectors in `lattice` of squared length two. -/
def roots : Set Space :=
  {x | x ∈ lattice ∧ squaredLength x = 2}

/-- Humphreys' displayed ordered base for the `E8` carrier. -/
def simpleRoot : Fin 8 → Space := ![
  ![-(1 : ℝ) / 2, (1 : ℝ) / 2, (1 : ℝ) / 2, (1 : ℝ) / 2,
    (1 : ℝ) / 2, (1 : ℝ) / 2, (1 : ℝ) / 2, -(1 : ℝ) / 2],
  ![1, 1, 0, 0, 0, 0, 0, 0],
  ![-1, 1, 0, 0, 0, 0, 0, 0],
  ![0, -1, 1, 0, 0, 0, 0, 0],
  ![0, 0, -1, 1, 0, 0, 0, 0],
  ![0, 0, 0, -1, 1, 0, 0, 0],
  ![0, 0, 0, 0, -1, 1, 0, 0],
  ![0, 0, 0, 0, 0, -1, 1, 0]]

/-- The set underlying Humphreys' displayed ordered `E8` base. -/
def simpleRoots : Set Space :=
  Set.range simpleRoot

/-- The ambient subspace of the canonical `E7` subsystem, spanned by the first seven numbered
simple roots. -/
def e7Span : Submodule ℝ Space :=
  Submodule.span ℝ (Set.range fun i : Fin 7 ↦ simpleRoot i.castSucc)

/-- The canonical `E7` subsystem of Humphreys' `E8` carrier. -/
def e7Roots : Set Space :=
  roots ∩ e7Span

/-- The ambient subspace of the canonical `E6` subsystem, spanned by the first six numbered
simple roots. -/
def e6Span : Submodule ℝ Space :=
  Submodule.span ℝ (Set.range fun i : Fin 6 ↦ simpleRoot (Fin.castAdd 2 i))

/-- The canonical `E6` subsystem of Humphreys' `E8` carrier. -/
def e6Roots : Set Space :=
  roots ∩ e6Span

end LeanCategories.HumphreysE8

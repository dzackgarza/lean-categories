/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# First-quadrant double complexes

Weibel, *An Introduction to Homological Algebra* (1994), §5.1, pp. 120--121
(FC05-C05-U001).

A first-quadrant double complex is represented by
`ChainComplex (ChainComplex C ℕ) ℕ`.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- First-quadrant double complexes, with the outer direction horizontal and
the inner direction vertical. -/
abbrev FirstQuadrantDoubleComplex (C : Type u) [Category.{v} C] [Abelian C] :=
  ChainComplex (ChainComplex C ℕ) ℕ

end LeanCategories.Homological

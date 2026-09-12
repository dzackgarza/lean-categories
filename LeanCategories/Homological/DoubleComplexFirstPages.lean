/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# First pages attached to a first-quadrant double complex

Weibel, *An Introduction to Homological Algebra* (1994), §5.1, pp. 120--121
(FC05-C05-U001).

A first-quadrant double complex is represented by
`ChainComplex (ChainComplex C ℕ) ℕ`.  Taking vertical homology degreewise gives
the horizontal complex whose `(p,q)` entry is `H_q^v(C_{p,*})`; taking its
horizontal homology gives `H_p^h H_q^v(C)`.

This file records these first two successive page objects.  The construction
of the spectral sequence itself and its abutment to the homology of the total
complex are result-level statements.
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

/-- Vertical homology in bidegree `(p,q)`. -/
noncomputable def doubleComplexE1
    (K : FirstQuadrantDoubleComplex C) (p q : ℕ) : C :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) q).obj (K.X p)

/-- The horizontal chain complex obtained by taking vertical homology in
fixed vertical degree `q`. -/
noncomputable def verticalHomologyComplex
    (K : FirstQuadrantDoubleComplex C) (q : ℕ) : ChainComplex C ℕ :=
  ((HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) q).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K

/-- The second page object `E²_{p,q}=H_p^h(H_q^v(K))`. -/
noncomputable def doubleComplexE2
    (K : FirstQuadrantDoubleComplex C) (p q : ℕ) : C :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) p).obj
    (verticalHomologyComplex K q)

end LeanCategories.Homological

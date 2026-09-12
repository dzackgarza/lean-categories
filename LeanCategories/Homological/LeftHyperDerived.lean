/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CEResolution
public import Mathlib.Algebra.Homology.TotalComplex

/-!
# Left hyper-derived objects

Weibel, *An Introduction to Homological Algebra* (1994), Definition 5.7.4,
pp. 145--149 (FC05-C05-U054).

For a right exact functor `F` and a chosen left C--E resolution `P → A`, the
left hyper-derived object in degree `n` is the degree-`n` homology of the
direct-sum total complex obtained by applying `F` degreewise to `P`.

Comparison between resolutions, independence of the choice, and functoriality
on complexes are result-level content and remain in the theorem sweep.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Apply an additive functor degreewise in both directions of a left C--E
resolution. -/
noncomputable def mapLeftCEDouble (F : C ⥤ D) [F.Additive]
    {A : ChainComplex C ℕ} (P : LeftCEResolution A) :
    ChainComplex (ChainComplex D ℕ) ℕ :=
  let G := F.mapHomologicalComplex (ComplexShape.down ℕ)
  (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.P

/-- Weibel's left hyper-derived object `𝕃_n F(A)` computed from a chosen
left C--E resolution. -/
noncomputable def leftHyperDerivedObject (F : C ⥤ D) [F.Additive]
    [PreservesFiniteColimits F]
    {A : ChainComplex C ℕ} (P : LeftCEResolution A)
    [HomologicalComplex₂.HasTotal (mapLeftCEDouble F P) (ComplexShape.down ℕ)]
    (n : ℕ) : D :=
  (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).obj
    (HomologicalComplex₂.total (mapLeftCEDouble F P) (ComplexShape.down ℕ))

end LeanCategories.Homological

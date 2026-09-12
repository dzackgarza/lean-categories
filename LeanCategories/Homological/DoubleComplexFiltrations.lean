/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DoubleComplexFirstPages
public import LeanCategories.Homological.FilteredComplex
public import Mathlib.Algebra.Homology.TotalComplex

/-!
# Column and row filtrations of a double complex

Weibel, *An Introduction to Homological Algebra* (1994), Definitions 5.6.1
and 5.6.2, pp. 141--144 (FC05-C05-U045, FC05-C05-U046).

For a first-quadrant double complex, the direct-sum total complex carries the
increasing column filtration and, dually, the increasing row filtration.  The
associated graded term in total degree `p+q` is respectively `C_{p,q}` and
`C_{q,p}`.  These conditions characterize the definition layer used below.

The resulting spectral-sequence page identifications and convergence are
result-level content and are not asserted here.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The associated graded complex of an increasing filtration on a
nonnegatively graded chain complex. -/
noncomputable def associatedGradedNat {K : ChainComplex C ℕ}
    (F : ChainComplexFiltration C (ComplexShape.down ℕ) K) (p : ℤ) :
    ChainComplex C ℕ :=
  cokernel (Subobject.ofLE (F.obj (p - 1)) (F.obj p) (F.monotone (by omega)))

/-- A realization of Weibel's column filtration on the direct-sum total
complex of a first-quadrant double complex. -/
structure ColumnFiltrationRealization
    (K : FirstQuadrantDoubleComplex C)
    [HomologicalComplex₂.HasTotal K (ComplexShape.down ℕ)] where
  /-- The increasing filtration on `Tot K`. -/
  filtration :
    ChainComplexFiltration C (ComplexShape.down ℕ)
      (HomologicalComplex₂.total K (ComplexShape.down ℕ))
  /-- Negative column filtration is zero. -/
  negative_isZero : ∀ (p : ℤ), p < 0 → ∀ n : ℕ,
    IsZero (filtration.degreeObject p n)
  /-- The associated graded object in filtration degree `p` is the `p`th
  column, with total degree `p+q`. -/
  graded_iso : ∀ (p q : ℕ),
    (associatedGradedNat filtration (p : ℤ)).X (p + q) ≅ (K.X p).X q

/-- The horizontal row complex `C_{*,q}` in a first-quadrant double complex. -/
noncomputable def horizontalRowComplex
    (K : FirstQuadrantDoubleComplex C) (q : ℕ) : ChainComplex C ℕ :=
  ((HomologicalComplex.eval C (ComplexShape.down ℕ) q).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K

/-- A realization of Weibel's row filtration on the direct-sum total complex. -/
structure RowFiltrationRealization
    (K : FirstQuadrantDoubleComplex C)
    [HomologicalComplex₂.HasTotal K (ComplexShape.down ℕ)] where
  /-- The increasing filtration on `Tot K`. -/
  filtration :
    ChainComplexFiltration C (ComplexShape.down ℕ)
      (HomologicalComplex₂.total K (ComplexShape.down ℕ))
  /-- Negative row filtration is zero. -/
  negative_isZero : ∀ (p : ℤ), p < 0 → ∀ n : ℕ,
    IsZero (filtration.degreeObject p n)
  /-- The associated graded object in filtration degree `p` is the `p`th
  row, with total degree `p+q`. -/
  graded_iso : ∀ (p q : ℕ),
    (associatedGradedNat filtration (p : ℤ)).X (p + q) ≅ (K.X q).X p

end LeanCategories.Homological

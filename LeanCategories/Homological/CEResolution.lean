/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DoubleComplexFiltrations
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Left C--E resolutions

Weibel, *An Introduction to Homological Algebra* (1994), Definition 5.7.1,
pp. 145--149 (FC05-C05-U051).

A left C--E resolution of a chain complex is a first-quadrant
double complex of projectives whose columns resolve the chain objects and whose
induced boundary and horizontal-homology complexes resolve the boundaries and
homology of the original complex.

Existence is Weibel's following lemma and remains theorem-layer.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Source-faithful data of a left C--E resolution. -/
structure LeftCEResolution (A : ChainComplex C ℕ) where
  /-- The resolving first-quadrant double complex. -/
  P : FirstQuadrantDoubleComplex C
  /-- Its degree-zero resolution row augments to the original complex. -/
  augmentation : horizontalRowComplex P 0 ⟶ A
  /-- Each column is identified with a projective resolution of the
  corresponding chain object. -/
  columnResolution : ∀ p : ℕ, ProjectiveResolution (A.X p)
  columnIso : ∀ p : ℕ, P.X p ≅ (columnResolution p).complex
  /-- The column augmentations agree with the double-complex augmentation in
  vertical degree zero. -/
  augmentation_compat : ∀ p : ℕ,
    (columnIso p).hom.f 0 ≫ (columnResolution p).π.f 0 = augmentation.f p
  /-- Every entry of the double complex is projective. -/
  projective : ∀ p q : ℕ, Projective ((P.X p).X q)
  /-- The vertical complex of horizontal boundaries resolves `B_p(A)`. -/
  boundaryResolution : ∀ p : ℕ,
    ProjectiveResolution (image (A.d (p + 1) p))
  boundaryIso : ∀ p : ℕ,
    image (P.d (p + 1) p) ≅ (boundaryResolution p).complex
  /-- The vertical complex of horizontal homology resolves `H_p(A)`. -/
  homologyResolution : ∀ p : ℕ,
    ProjectiveResolution (A.homology p)
  homologyIso : ∀ p : ℕ,
    P.homology p ≅ (homologyResolution p).complex
  /-- Weibel's support condition: a zero chain object has a zero resolving
  column. -/
  zero_column : ∀ p : ℕ, IsZero (A.X p) → ∀ q : ℕ, IsZero ((P.X p).X q)

end LeanCategories.Homological

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Right C--E resolutions and hyper-derived objects

Weibel, *An Introduction to Homological Algebra* (1994), Construction 5.7.9,
pp. 145--149 (FC05-C05-U059).

This is the cohomological dual of the projective C--E resolution: a
first-quadrant cochain bicomplex of injectives resolving the cochain objects,
their coboundaries, and their cohomology.  Applying an additive functor and
taking the total cohomology gives the source definition of the right
hyper-derived object.

Existence, comparison between choices, functoriality, and the resulting
spectral sequences are theorem-layer.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The horizontal row `I^{*,q}` of a first-quadrant cochain bicomplex. -/
noncomputable def horizontalRowCochainComplex
    (I : CochainComplex (CochainComplex C ℕ) ℕ) (q : ℕ) : CochainComplex C ℕ :=
  ((HomologicalComplex.eval C (ComplexShape.up ℕ) q).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj I

/-- Source-faithful data of a right C--E resolution of a cochain complex. -/
structure RightCEResolution (A : CochainComplex C ℕ) where
  /-- The resolving cochain bicomplex. -/
  I : CochainComplex (CochainComplex C ℕ) ℕ
  /-- The original complex maps into the degree-zero resolution row. -/
  augmentation : A ⟶ horizontalRowCochainComplex I 0
  /-- Each column is an injective resolution of the corresponding cochain
  object. -/
  columnResolution : ∀ p : ℕ, InjectiveResolution (A.X p)
  columnIso : ∀ p : ℕ, I.X p ≅ (columnResolution p).cocomplex
  /-- Compatibility of the column inclusions with the bicomplex augmentation. -/
  augmentation_compat : ∀ p : ℕ,
    augmentation.f p ≫ (columnIso p).hom.f 0 = (columnResolution p).ι.f 0
  /-- Every bicomplex entry is injective. -/
  injective : ∀ p q : ℕ, Injective ((I.X p).X q)
  /-- The vertical complex of horizontal coboundaries resolves the coboundary
  object of `A`. -/
  boundaryResolution : ∀ p : ℕ,
    InjectiveResolution (image (A.d p (p + 1)))
  boundaryIso : ∀ p : ℕ,
    image (I.d p (p + 1)) ≅ (boundaryResolution p).cocomplex
  /-- The vertical complex of horizontal cohomology resolves `H^p(A)`. -/
  homologyResolution : ∀ p : ℕ,
    InjectiveResolution (A.homology p)
  homologyIso : ∀ p : ℕ,
    I.homology p ≅ (homologyResolution p).cocomplex
  /-- A zero source term has a zero resolving column. -/
  zero_column : ∀ p : ℕ, IsZero (A.X p) → ∀ q : ℕ, IsZero ((I.X p).X q)

variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Apply an additive functor degreewise to a right C--E bicomplex. -/
noncomputable def mapRightCEDouble (F : C ⥤ D) [F.Additive]
    {A : CochainComplex C ℕ} (J : RightCEResolution A) :
    CochainComplex (CochainComplex D ℕ) ℕ :=
  let G := F.mapHomologicalComplex (ComplexShape.up ℕ)
  (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.I

/-- Extend both nonnegative cohomological axes by zero to `ℤ`, where Mathlib's
canonical cohomological total-complex signs are available. -/
noncomputable def mapRightCEDoubleInt (F : C ⥤ D) [F.Additive]
    {A : CochainComplex C ℕ} (J : RightCEResolution A) :
    CochainComplex (CochainComplex D ℤ) ℤ :=
  let innerExtend := ComplexShape.embeddingUpNat.extendFunctor D
  let K : CochainComplex (CochainComplex D ℤ) ℕ :=
    (innerExtend.mapHomologicalComplex (ComplexShape.up ℕ)).obj (mapRightCEDouble F J)
  (ComplexShape.embeddingUpNat.extendFunctor (CochainComplex D ℤ)).obj K

/-- The right hyper-derived object computed from a chosen right C--E
resolution and a chosen totalization. -/
noncomputable def rightHyperDerivedObject (F : C ⥤ D) [F.Additive]
    {A : CochainComplex C ℕ} (J : RightCEResolution A)
    [HomologicalComplex₂.HasTotal (mapRightCEDoubleInt F J) (ComplexShape.up ℤ)]
    (n : ℕ) : D :=
  (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)).obj
    (HomologicalComplex₂.total (mapRightCEDoubleInt F J) (ComplexShape.up ℤ))

end LeanCategories.Homological

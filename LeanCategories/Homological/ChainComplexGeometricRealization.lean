/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CWSpectrum
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Geometric realization of chain complexes as CW spectra

Weibel, *An Introduction to Homological Algebra* (1994), Geometric
Realization 10.9.19, §10.9, pp. 407--416 (FC05-C10-U120).

For an unbounded chain complex of abelian groups, the `n`th spectrum level is
constructed by shifting the complex, taking its good nonnegative truncation,
applying inverse Dold--Kan, and geometrically realizing the resulting
simplicial abelian group.  These levels assemble into a CW spectrum, functorial
in the chain complex.

The facts that this functor takes quasi-isomorphisms to weak equivalences and
intertwines translation with looping are theorem-layer statements and are not
asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace LeanCategories.Homological

universe u

/-- Forget the abelian-group structure of a simplicial abelian group. -/
def simplicialAbelianUnderlyingSSet
    (A : SimplicialObject AddCommGrpCat.{u}) : SSet.{u} :=
  A ⋙ forget AddCommGrpCat

/-- Inverse Dold--Kan applied to a nonnegative chain complex. -/
def doldKanSimplicialAbelian
    (K : ChainComplex AddCommGrpCat.{u} ℕ) :
    SimplicialObject AddCommGrpCat.{u} :=
  CategoryTheory.Abelian.DoldKan.Γ.obj K

/-- The ordinary geometric realization of the underlying simplicial set of
inverse Dold--Kan. -/
def doldKanGeometricTop
    (K : ChainComplex AddCommGrpCat.{u} ℕ) : TopCat.{u} :=
  SSet.toTop.obj
    (simplicialAbelianUnderlyingSSet (doldKanSimplicialAbelian K))

/-- Source-faithful data of the shift and good truncation used for the `n`th
space in Weibel's realization.

The shifted complex has degree `i` identified with the original degree
`i+n`.  Its good truncation keeps the positive degrees and replaces degree
zero by the cycle object, with the differential `1 → 0` induced by the
original differential.
-/
structure GoodTruncationStage
    (C : ChainComplex AddCommGrpCat.{u} ℤ) (n : ℕ) where
  /-- The shifted integer-indexed complex. -/
  shifted : ChainComplex AddCommGrpCat.{u} ℤ
  /-- Degree identification for the shift. -/
  shiftedDegreeIso : ∀ i : ℤ,
    shifted.X i ≅ C.X (i + (n : ℤ))
  /-- Compatibility of the shifted differential with the original one. -/
  shifted_d : ∀ i : ℤ,
    (shiftedDegreeIso i).hom ≫
        C.d (i + (n : ℤ)) (i - 1 + (n : ℤ)) =
      shifted.d i (i - 1) ≫ (shiftedDegreeIso (i - 1)).hom
  /-- The good nonnegative truncation. -/
  truncated : ChainComplex AddCommGrpCat.{u} ℕ
  /-- Degree zero is the cycle object of the shifted complex. -/
  zeroIso : truncated.X 0 ≅ shifted.cycles 0
  /-- Positive degrees agree with the shifted complex. -/
  positiveIso : ∀ i : ℕ,
    truncated.X (i + 1) ≅ shifted.X ((i + 1 : ℕ) : ℤ)
  /-- The differential from degree one to zero is the canonical map to cycles. -/
  d_one_zero :
    (positiveIso 0).hom ≫ shifted.toCycles 1 0 =
      truncated.d 1 0 ≫ zeroIso.hom
  /-- Positive differentials are inherited from the shifted complex. -/
  d_positive : ∀ i : ℕ,
    (positiveIso (i + 1)).hom ≫
        shifted.d ((i + 2 : ℕ) : ℤ) ((i + 1 : ℕ) : ℤ) =
      truncated.d (i + 2) (i + 1) ≫ (positiveIso i).hom

/-- The Dold--Kan/geometric-realization stage producing one based spectrum
level from a shifted good truncation. -/
structure DoldKanGeometricLevel
    (C : ChainComplex AddCommGrpCat.{u} ℤ) (n : ℕ) where
  /-- The shifted good truncation. -/
  truncation : GoodTruncationStage C n
  /-- The based realization; its basepoint is induced by the zero simplex. -/
  basedSpace : LeanCategories.Topology.BasedTop.{u}
  /-- The underlying space is the geometric realization of inverse Dold--Kan. -/
  realizationIso : basedSpace.right ≅ doldKanGeometricTop truncation.truncated

/-- A source-faithful realization of the spectrum associated to one chain
complex by Weibel's construction. -/
structure ChainComplexSpectrumRealization
    (C : ChainComplex AddCommGrpCat.{u} ℤ) where
  /-- Dold--Kan/geometric-realization data in every spectrum degree. -/
  level : ∀ n : ℕ, DoldKanGeometricLevel C n
  /-- The spectrum assembled from those spaces. -/
  spectrum : Spectrum.{u}
  /-- Identification of its levels with the realized spaces above. -/
  levelIso : ∀ n : ℕ, spectrum.space n ≅ (level n).basedSpace
  /-- The resulting spectrum lies in `S_CW`. -/
  isCW : IsCWSpectrum spectrum

/-- Definition-layer realization of Weibel's geometric realization functor
`Ch(Ab) → S_CW`. -/
structure ChainComplexGeometricRealization where
  /-- The underlying functor to spectra. -/
  functor : ChainComplex AddCommGrpCat.{u} ℤ ⥤ Spectrum.{u}
  /-- Source construction data for each object. -/
  objectData : ∀ C : ChainComplex AddCommGrpCat.{u} ℤ,
    ChainComplexSpectrumRealization C
  /-- The functor object is the spectrum assembled by the source construction. -/
  objectIso : ∀ C : ChainComplex AddCommGrpCat.{u} ℤ,
    (objectData C).spectrum ≅ functor.obj C
  /-- Every functor value is a CW spectrum. -/
  isCW : ∀ C : ChainComplex AddCommGrpCat.{u} ℤ,
    IsCWSpectrum (functor.obj C)

/-- Weibel's geometric-realization functor with codomain restricted to the
full subcategory `S_CW`.

Source: Weibel, Geometric Realization 10.9.19 (FC05-C10-U120). -/
def ChainComplexGeometricRealization.toCWFunctor
    (G : ChainComplexGeometricRealization.{u}) :
    ChainComplex AddCommGrpCat.{u} ℤ ⥤ CWSpectrum.{u} :=
  ObjectProperty.lift cwSpectrumProperty G.functor G.isCW

end LeanCategories.Homological

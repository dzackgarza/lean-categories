/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Projective varieties and `Proj`

Mathlib owns the standard projective-spectrum and `Proj` constructions.  This
module exposes those constructions under project-specific catalogue names.
It does not introduce a second variety hierarchy or a projective-morphism
predicate that Mathlib does not provide.

The source implementation is in
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/{Topology,StructureSheaf,Scheme,Basic}.lean`.
-/

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.Topology.Category.TopCat.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace LeanCategories.Schemes

universe u

variable {A σ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-! ### Projective spectrum and homogeneous coordinates -/

/-- The graded piece containing homogeneous coordinates of degree `n`. -/
abbrev ProjGradedPiece (n : ℕ) : Type u := 𝒜 n

/-- Homogeneous ideals for the graded ring used by `Proj`. -/
abbrev ProjHomogeneousIdeal : Type u := HomogeneousIdeal 𝒜

/-- The projective spectrum of a graded ring, as a topological object. -/
abbrev ProjectiveSpectrumTopCat : TopCat.{u} :=
  TopCat.of (ProjectiveSpectrum 𝒜)

/-- A projective-spectrum closed set defined by homogeneous equations. -/
abbrev projectiveSpectrumClosedSet (s : Set A) : Set (ProjectiveSpectrum 𝒜) :=
  ProjectiveSpectrum.zeroLocus 𝒜 s

/-- The homogeneous vanishing ideal of a subset of the projective spectrum. -/
abbrev projectiveSpectrumVanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) :
    HomogeneousIdeal 𝒜 :=
  ProjectiveSpectrum.vanishingIdeal 𝒜 t

/-- The basic projective open `D₊(f)`. -/
abbrev projectiveSpectrumBasicOpen (f : A) : TopologicalSpace.Opens (ProjectiveSpectrum 𝒜) :=
  ProjectiveSpectrum.basicOpen 𝒜 f

/-! ### The projective scheme -/

/-- The scheme `Proj(𝒜)` attached to an `ℕ`-graded commutative ring. -/
abbrev ProjScheme : Type (u + 1) := AlgebraicGeometry.Proj 𝒜

/-- The projective basic open `D₊(f)` as an open subscheme of `Proj(𝒜)`. -/
abbrev projBasicOpen (f : A) : (AlgebraicGeometry.Proj 𝒜).Opens :=
  AlgebraicGeometry.Proj.basicOpen 𝒜 f

/-- The structure morphism `Proj(𝒜) ⟶ Spec(𝒜 0)`. -/
abbrev projToSpecZero : AlgebraicGeometry.Proj 𝒜 ⟶
    Spec (.of (𝒜 0)) :=
  AlgebraicGeometry.Proj.toSpecZero 𝒜

/-- The affine chart of `Proj(𝒜)` at a positive-degree homogeneous element. -/
abbrev projBasicOpenIsoSpec {f : A} {n : ℕ} (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    (projBasicOpen 𝒜 f).toScheme ≅ Spec (.of (HomogeneousLocalization.Away 𝒜 f)) :=
  AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 hf hn

/-- The canonical affine open immersion into `Proj(𝒜)`. -/
abbrev projAwayOpenImmersion {f : A} {n : ℕ} (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    Spec (.of (HomogeneousLocalization.Away 𝒜 f)) ⟶ AlgebraicGeometry.Proj 𝒜 :=
  AlgebraicGeometry.Proj.awayι 𝒜 hf hn

/-- The canonical affine open cover of `Proj(𝒜)` by positive-degree charts. -/
abbrev projAffineOpenCover : (AlgebraicGeometry.Proj 𝒜).AffineOpenCover :=
  AlgebraicGeometry.Proj.affineOpenCover 𝒜

/-- The stalk of `Proj(𝒜)` at a projective-spectrum point. -/
abbrev projStalkIso (x : ProjectiveSpectrum.top 𝒜) :
    (AlgebraicGeometry.Proj 𝒜).presheaf.stalk x ≅
      .of (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :=
  AlgebraicGeometry.Proj.stalkIso 𝒜 x

end LeanCategories.Schemes

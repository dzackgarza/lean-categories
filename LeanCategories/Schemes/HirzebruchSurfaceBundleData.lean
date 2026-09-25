/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.ProjectiveBundleData
public import LeanCategories.AlgebraicGeometry.AmpleSheaf
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Hirzebruch-surface projective-bundle data

Definition-level support for Peters--Sterk FC11-B-U024.

For the Grothendieck quotient convention

  `F_n = P_{P^1}(O ⊕ O(n))`,

the distinguished negative section is induced by the canonical quotient
`O ⊕ O(n) → O`.  The generic projective-bundle owner already records
`P(E) = Proj Sym(E)` and its selected `O(1)`.  This file specializes that
owner far enough to construct the source bundle module and the canonical line
quotient without proving local freeness, finite presentation, noetherianity,
or any intersection statement.

The remaining quotient-to-section map is deliberately not fabricated here:
`ProjectiveBundleData` currently exposes the projective-bundle scheme,
projection, and twisting sheaf, but not the universal quotient
`π^*E → O_{P(E)}(1)` or the induced map from a line quotient of `E`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open LeanCategories.AlgebraicGeometry

namespace LeanCategories.Schemes

/-- The complex point used as the base of the projective-line construction. -/
abbrev hirzebruchComplexPointData : Scheme :=
  Spec (.of ℂ)

/-- The rank-two free module `O ⊕ O` over the complex point. -/
abbrev hirzebruchProjectiveLineModuleData :
    hirzebruchComplexPointData.Modules :=
  schemeModuleUnit hirzebruchComplexPointData ⊞
    schemeModuleUnit hirzebruchComplexPointData

/-- Exact projective-bundle specification for the projective line
`P(O ⊕ O)` over the complex point.

The class-valued geometric hypotheses are retained existentially.  Their
verification is theorem content; no instance proof is manufactured in
Sweep III. -/
def IsHirzebruchProjectiveLineData
    (P : RelativeProjCandidateData hirzebruchComplexPointData) : Prop :=
  ∃ (hN : AlgebraicGeometry.IsNoetherian hirzebruchComplexPointData)
      (hLF : hirzebruchProjectiveLineModuleData.IsLocallyFree)
      (hFP : hirzebruchProjectiveLineModuleData.IsFinitePresentation),
    letI := hN
    letI := hLF
    letI := hFP
    IsProjectiveBundleData hirzebruchProjectiveLineModuleData P

/-- The supplied tautological `O(1)` candidate on a projective-line
presentation.  Source-faithfulness of the ambient projective line is recorded
separately by `IsHirzebruchProjectiveLineData`. -/
abbrev hirzebruchProjectiveLineTwistData
    (P : RelativeProjCandidateData hirzebruchComplexPointData) :
    P.scheme.Modules :=
  P.twistOne

/-- The rank-two bundle `O ⊕ O(n)` on a supplied projective-line
presentation. -/
abbrev hirzebruchBundleModuleData
    (P : RelativeProjCandidateData hirzebruchComplexPointData) (n : ℕ) :
    P.scheme.Modules :=
  schemeModuleUnit P.scheme ⊞
    schemeModuleTensorPower (hirzebruchProjectiveLineTwistData P) n

/-- The canonical line quotient `O ⊕ O(n) → O` whose projectivized
quotient section is the distinguished negative section of `F_n`. -/
def hirzebruchNegativeSectionQuotientData
    (P : RelativeProjCandidateData hirzebruchComplexPointData) (n : ℕ) :
    hirzebruchBundleModuleData P n ⟶ schemeModuleUnit P.scheme :=
  biprod.fst

/-- Exact projective-bundle specification for
`F_n = P_{P¹}(O ⊕ O(n))`.

The noetherian/local-freeness/finite-presentation hypotheses needed by the
generic projective-bundle owner remain propositionally quantified.  Proving
them is result work, not part of this definition-level construction. -/
def IsHirzebruchSurfaceBundleData
    (P : RelativeProjCandidateData hirzebruchComplexPointData) (n : ℕ)
    (F : RelativeProjCandidateData P.scheme) : Prop :=
  ∃ (hN : AlgebraicGeometry.IsNoetherian P.scheme)
      (hLF : (hirzebruchBundleModuleData P n).IsLocallyFree)
      (hFP : (hirzebruchBundleModuleData P n).IsFinitePresentation),
    letI := hN
    letI := hLF
    letI := hFP
    IsProjectiveBundleData (hirzebruchBundleModuleData P n) F

/-- Proof-free candidate presentation of a Hirzebruch surface: a candidate
projective line together with a candidate projective bundle over it. -/
structure HirzebruchSurfacePresentationData (n : ℕ) where
  projectiveLine : RelativeProjCandidateData hirzebruchComplexPointData
  surface : RelativeProjCandidateData projectiveLine.scheme

/-- Exact source-faithfulness predicate for supplied Hirzebruch-surface
presentation data. -/
def IsHirzebruchSurfacePresentationData (n : ℕ)
    (D : HirzebruchSurfacePresentationData n) : Prop :=
  IsHirzebruchProjectiveLineData D.projectiveLine ∧
    IsHirzebruchSurfaceBundleData D.projectiveLine n D.surface

/-- The scheme underlying supplied Hirzebruch-surface presentation data. -/
abbrev hirzebruchSurfaceSchemeData {n : ℕ}
    (D : HirzebruchSurfacePresentationData n) : Scheme :=
  D.surface.scheme

/-- The structural projection `F_n → P¹`. -/
def hirzebruchSurfaceProjectionData {n : ℕ}
    (D : HirzebruchSurfacePresentationData n) :
    hirzebruchSurfaceSchemeData D ⟶ D.projectiveLine.scheme :=
  D.surface.projection

end LeanCategories.Schemes

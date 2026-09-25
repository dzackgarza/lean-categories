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

/-- The selected projective-line projective-bundle datum
`P_{Spec ℂ}(O ⊕ O)`.

As for the generic relative-Proj and projective-bundle owners, the existence
theorem establishing `IsHirzebruchProjectiveLineData` is deliberately not
proved in Sweep III. -/
def hirzebruchProjectiveLineData :
    RelativeProjCandidateData hirzebruchComplexPointData :=
  Classical.epsilon IsHirzebruchProjectiveLineData

/-- The selected tautological `O(1)` on the projective line. -/
abbrev hirzebruchProjectiveLineTwistData :
    hirzebruchProjectiveLineData.scheme.Modules :=
  hirzebruchProjectiveLineData.twistOne

/-- The rank-two bundle `O ⊕ O(n)` on the selected projective line. -/
abbrev hirzebruchBundleModuleData (n : ℕ) :
    hirzebruchProjectiveLineData.scheme.Modules :=
  schemeModuleUnit hirzebruchProjectiveLineData.scheme ⊞
    schemeModuleTensorPower hirzebruchProjectiveLineTwistData n

/-- The canonical line quotient `O ⊕ O(n) → O` whose projectivized
quotient section is the distinguished negative section of `F_n`. -/
def hirzebruchNegativeSectionQuotientData (n : ℕ) :
    hirzebruchBundleModuleData n ⟶
      schemeModuleUnit hirzebruchProjectiveLineData.scheme :=
  biprod.fst

/-- Exact projective-bundle specification for
`F_n = P_{P¹}(O ⊕ O(n))`.

The noetherian/local-freeness/finite-presentation hypotheses needed by the
generic projective-bundle owner remain propositionally quantified.  Proving
them is result work, not part of this definition-level construction. -/
def IsHirzebruchSurfaceBundleData (n : ℕ)
    (P : RelativeProjCandidateData hirzebruchProjectiveLineData.scheme) : Prop :=
  ∃ (hN : AlgebraicGeometry.IsNoetherian hirzebruchProjectiveLineData.scheme)
      (hLF : (hirzebruchBundleModuleData n).IsLocallyFree)
      (hFP : (hirzebruchBundleModuleData n).IsFinitePresentation),
    letI := hN
    letI := hLF
    letI := hFP
    IsProjectiveBundleData (hirzebruchBundleModuleData n) P

/-- The selected Hirzebruch-surface projective-bundle datum
`P_{P¹}(O ⊕ O(n))`. -/
def hirzebruchSurfaceBundleData (n : ℕ) :
    RelativeProjCandidateData hirzebruchProjectiveLineData.scheme :=
  Classical.epsilon (IsHirzebruchSurfaceBundleData n)

/-- The scheme underlying the selected Hirzebruch-surface bundle. -/
abbrev hirzebruchSurfaceSchemeData (n : ℕ) : Scheme :=
  (hirzebruchSurfaceBundleData n).scheme

/-- The structural projection `F_n → P¹`. -/
def hirzebruchSurfaceProjectionData (n : ℕ) :
    hirzebruchSurfaceSchemeData n ⟶ hirzebruchProjectiveLineData.scheme :=
  (hirzebruchSurfaceBundleData n).projection

end LeanCategories.Schemes

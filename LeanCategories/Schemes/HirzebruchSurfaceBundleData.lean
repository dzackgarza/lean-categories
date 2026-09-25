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

end LeanCategories.Schemes

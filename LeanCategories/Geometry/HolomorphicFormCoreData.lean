/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Sheaf.Basic
public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Analysis.Complex.Basic

/-!
# Holomorphic differential-form core data

The reusable definition-level core of the holomorphic-form stack: the actual
bundle of continuous alternating complex covectors and its sheaf of analytic
sections.  It is intentionally independent of later additive/sheaf-cohomology
machinery so geometric definitions such as the canonical bundle can reuse the
constructed object directly.
-/

@[expose] public noncomputable section

open Bundle
open CategoryTheory
open scoped ContDiff Manifold Topology

namespace LeanCategories.Geometry

universe u

variable {E H X : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [TopologicalSpace H]
variable (I : ModelWithCorners ℂ E H) [I.Boundaryless]
variable [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ω X]

/-- Model fibre for holomorphic `p`-forms on a complex manifold modelled on
`E`: continuous alternating `p`-linear forms on `E`. -/
abbrev CanonicalPFormModelFiberData (p : ℕ) :=
  E [⋀^Fin p]→L[ℂ] ℂ

/-- Fibre of holomorphic `p`-forms at `x`, represented by continuous
alternating complex-multilinear forms on the tangent space at `x`. -/
abbrev CanonicalPFormFiberData (p : ℕ) (x : X) :=
  TangentSpace I x [⋀^Fin p]→L[ℂ] ℂ

/-- Total space of the bundle whose fibres are holomorphic `p`-form fibres. -/
abbrev CanonicalPFormBundleData (p : ℕ) :=
  TotalSpace (CanonicalPFormModelFiberData (E := E) p)
    (CanonicalPFormFiberData (X := X) I p)

/-- The local condition defining a holomorphic `p`-form: an analytic map into
the native alternating-form bundle which is actually a section of that bundle. -/
def canonicalPFormLocalPredicateData (p : ℕ) :
    TopCat.LocalPredicate (fun _ : TopCat.of X => CanonicalPFormBundleData (X := X) I p) :=
  ((contDiffWithinAt_localInvariantProp
      (I := I)
      (I' := I.prod 𝓘(ℂ, CanonicalPFormModelFiberData (E := E) p))
      ω).localPredicate X (CanonicalPFormBundleData (X := X) I p)).and
    (TopCat.isSection (X := TopCat.of X)
      (Bundle.TotalSpace.proj : CanonicalPFormBundleData (X := X) I p → X))

/-- Sheaf `Ω_X^p` of holomorphic `p`-forms on a complex manifold. -/
def canonicalPFormSheafData (p : ℕ) :
    TopCat.Sheaf (Type u) (TopCat.of X) :=
  TopCat.subsheafToTypes (canonicalPFormLocalPredicateData (X := X) I p)

/-- Fibre value of a section of the holomorphic-form sheaf. -/
def canonicalPFormSectionValueData
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s : (canonicalPFormSheafData (X := X) I p).presheaf.obj U)
    (x : U.unop) :
    CanonicalPFormFiberData (X := X) I p x.1 :=
  cast
    (congrArg
      (CanonicalPFormFiberData (X := X) I p)
      (congrFun s.2.2 x))
    (s.1 x).2

end LeanCategories.Geometry

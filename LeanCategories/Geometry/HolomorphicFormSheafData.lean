/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Sheaf.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Analysis.Complex.Basic

/-!
# Holomorphic differential-form sheaf data on complex manifolds

Definition-level carrier for Peters--Sterk FC11-B-U003, with the top-degree
specialization needed by FC11-B-U042.

For a complex manifold modelled on `E`, a fibre of the bundle of holomorphic
`p`-forms is represented by continuous alternating complex-multilinear maps
`(T_x X)^p → ℂ`. Mathlib's tangent-bundle and continuous-alternating-map
bundle constructions supply this bundle directly. Its sheaf of holomorphic
sections is the subsheaf of complex-smooth maps into the total space whose
bundle projection is the identity on the base.

No Hodge-cohomology, finite-dimensionality, canonical-divisor, or
pluricanonical result is asserted here.
-/

@[expose] public noncomputable section

open Bundle
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
abbrev HolomorphicPFormModelFiberData (p : ℕ) :=
  E [⋀^Fin p]→L[ℂ] ℂ

/-- Fibre of holomorphic `p`-forms at `x`, represented by continuous
alternating complex-multilinear forms on the tangent space at `x`. -/
abbrev HolomorphicPFormFiberData (p : ℕ) (x : X) :=
  TangentSpace I x [⋀^Fin p]→L[ℂ] ℂ

/-- Total space of the bundle whose fibres are holomorphic `p`-form fibres. -/
abbrev HolomorphicPFormBundleData (p : ℕ) :=
  TotalSpace (HolomorphicPFormModelFiberData (E := E) p)
    (HolomorphicPFormFiberData (X := X) I p)

/-- The local condition defining a holomorphic `p`-form: an analytic map into
the native alternating-form bundle which is actually a section of that bundle.

The first conjunct uses Mathlib's manifold sheaf machinery at analytic
regularity `ω`; the second conjunct is the native `TopCat.isSection` local
predicate for the bundle projection. -/
def holomorphicPFormLocalPredicateData (p : ℕ) :
    TopCat.LocalPredicate (fun _ : TopCat.of X => HolomorphicPFormBundleData (X := X) I p) :=
  ((contDiffWithinAt_localInvariantProp
      (I := I)
      (I' := I.prod 𝓘(ℂ, HolomorphicPFormModelFiberData (E := E) p))
      ω).localPredicate X (HolomorphicPFormBundleData (X := X) I p)).and
    (TopCat.isSection (X := TopCat.of X)
      (Bundle.TotalSpace.proj : HolomorphicPFormBundleData (X := X) I p → X))

/-- Sheaf `Ω_X^p` of holomorphic `p`-forms on a complex manifold.  Its sections
over an open set are exactly analytic sections of the native bundle of
continuous alternating complex `p`-covectors. -/
def holomorphicPFormSheafData (p : ℕ) :
    TopCat.Sheaf (Type u) (TopCat.of X) :=
  TopCat.subsheafToTypes (holomorphicPFormLocalPredicateData (X := X) I p)

/-- Native holomorphic cotangent bundle (`p = 1`). -/
abbrev HolomorphicCotangentBundleData :=
  HolomorphicPFormBundleData (X := X) I 1

/-- Sheaf of holomorphic one-forms, i.e. the holomorphic cotangent sheaf. -/
abbrev holomorphicCotangentSheafData :=
  holomorphicPFormSheafData (X := X) I 1

/-- The `p`-th exterior-power cotangent-bundle carrier.  It is represented
fibrewise by alternating complex `p`-covectors. -/
abbrev HolomorphicCotangentExteriorPowerBundleData (p : ℕ) :=
  HolomorphicPFormBundleData (X := X) I p

variable [FiniteDimensional ℂ E]

/-- Top holomorphic-form bundle. For a complex manifold modelled on the
finite-dimensional complex space `E`, its degree is `finrank ℂ E`. -/
abbrev CanonicalTopFormBundleData :=
  HolomorphicPFormBundleData (X := X) I (Module.finrank ℂ E)

/-- Sheaf of holomorphic top forms, the sheaf underlying the canonical bundle. -/
abbrev canonicalTopFormSheafData :=
  holomorphicPFormSheafData (X := X) I (Module.finrank ℂ E)

end LeanCategories.Geometry

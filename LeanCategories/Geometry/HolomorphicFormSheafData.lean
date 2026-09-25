/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Sheaf.Basic
public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.CategoryTheory.Sites.Adjunction

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

/-- Raw additive/complex-linear presentation data for the holomorphic
`p`-form sheaf.

The additive sheaf is the coefficient object needed by Mathlib's native sheaf
cohomology.  The family `scalar c` records scalar multiplication by
`c : ℂ` as endomorphisms of that same sheaf; using sheaf morphisms makes
compatibility with restriction maps part of the ambient categorical data. -/
structure HolomorphicPFormLinearSheafPresentationData where
  sheaf : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X)
  scalar : ℂ → (sheaf ⟶ sheaf)

/-- Forget the additive structure of a proposed linear presentation. -/
def holomorphicPFormForgottenSheafData
    (D : HolomorphicPFormLinearSheafPresentationData (X := X)) :
    TopCat.Sheaf (Type u) (TopCat.of X) :=
  (CategoryTheory.sheafForget
    (D := AddCommGrpCat.{u})
    (Opens.grothendieckTopology (TopCat.of X))).obj D.sheaf

/-- Transport a section of an additive presentation to the already-realized
Type-valued sheaf, under an exact equality of the forgotten sheaves. -/
def holomorphicPFormTransportSectionData
    (p : ℕ) (D : HolomorphicPFormLinearSheafPresentationData (X := X))
    (h : holomorphicPFormForgottenSheafData (X := X) D =
      holomorphicPFormSheafData (X := X) I p)
    (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s : D.sheaf.presheaf.obj U) :
    (holomorphicPFormSheafData (X := X) I p).presheaf.obj U :=
  cast
    (congrArg
      (fun F : TopCat.Sheaf (Type u) (TopCat.of X) => F.presheaf.obj U)
      h)
    s

/-- Fibre value of a section of the realized Type-valued holomorphic-form
sheaf.  The section equation supplies the transport from the total-space fibre
over its recorded base point to the fibre over the actual point of the open
set. -/
def holomorphicPFormSectionValueData
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U)
    (x : U.unop) :
    HolomorphicPFormFiberData (X := X) I p x.1 :=
  cast
    (congrArg
      (HolomorphicPFormFiberData (X := X) I p)
      (congrFun s.2.2 x))
    (s.1 x).2

/-- Exact pointwise graph for zero in the holomorphic-form sheaf. -/
def IsHolomorphicPFormZeroSectionData
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U) : Prop :=
  ∀ x : U.unop, holomorphicPFormSectionValueData (X := X) I p U s x = 0

/-- Exact pointwise graph for addition of holomorphic `p`-forms. -/
def IsHolomorphicPFormAddSectionData
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s t r : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U) : Prop :=
  ∀ x : U.unop,
    holomorphicPFormSectionValueData (X := X) I p U r x =
      holomorphicPFormSectionValueData (X := X) I p U s x +
        holomorphicPFormSectionValueData (X := X) I p U t x

/-- Exact pointwise graph for additive inverse of a holomorphic `p`-form. -/
def IsHolomorphicPFormNegSectionData
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s r : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U) : Prop :=
  ∀ x : U.unop,
    holomorphicPFormSectionValueData (X := X) I p U r x =
      -holomorphicPFormSectionValueData (X := X) I p U s x

/-- Exact pointwise graph for constant complex scalar multiplication of a
holomorphic `p`-form. -/
def IsHolomorphicPFormSMulSectionData
    (p : ℕ) (c : ℂ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s r : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U) : Prop :=
  ∀ x : U.unop,
    holomorphicPFormSectionValueData (X := X) I p U r x =
      c • holomorphicPFormSectionValueData (X := X) I p U s x

/-- Exact presentation predicate for the canonical additive and complex-linear
refinement of `Ω_X^p`.

The forgotten sheaf is required to be exactly the already-realized
`holomorphicPFormSheafData`.  Its zero, addition and inverse are required to
have the fibrewise graphs inherited from the alternating-form fibres, and each
complex scalar is required to act pointwise by the native scalar multiplication.
Because scalar maps are sheaf endomorphisms and the additive restrictions are
morphisms in `AddCommGrpCat`, restriction compatibility is already carried by
the ambient sheaf structure rather than reproved here. -/
def IsHolomorphicPFormLinearSheafPresentationData
    (p : ℕ) (D : HolomorphicPFormLinearSheafPresentationData (X := X)) : Prop :=
  ∃ h : holomorphicPFormForgottenSheafData (X := X) D =
      holomorphicPFormSheafData (X := X) I p,
    (∀ U,
      IsHolomorphicPFormZeroSectionData (X := X) I p U
        (holomorphicPFormTransportSectionData (X := X) I p D h U 0)) ∧
    (∀ U (s t : D.sheaf.presheaf.obj U),
      IsHolomorphicPFormAddSectionData (X := X) I p U
        (holomorphicPFormTransportSectionData (X := X) I p D h U s)
        (holomorphicPFormTransportSectionData (X := X) I p D h U t)
        (holomorphicPFormTransportSectionData (X := X) I p D h U (s + t))) ∧
    (∀ U (s : D.sheaf.presheaf.obj U),
      IsHolomorphicPFormNegSectionData (X := X) I p U
        (holomorphicPFormTransportSectionData (X := X) I p D h U s)
        (holomorphicPFormTransportSectionData (X := X) I p D h U (-s))) ∧
    ∀ (c : ℂ) U (s : D.sheaf.presheaf.obj U),
      IsHolomorphicPFormSMulSectionData (X := X) I p c U
        (holomorphicPFormTransportSectionData (X := X) I p D h U s)
        (holomorphicPFormTransportSectionData (X := X) I p D h U
          ((D.scalar c).hom.app U s))

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

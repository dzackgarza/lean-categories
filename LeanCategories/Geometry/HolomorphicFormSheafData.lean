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
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits

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

section SmoothModuleSheaf

variable [IsManifold I ∞ X]

/-- Reconstruct a holomorphic-form section from its fibre values.  The equality
is literal on the total-space presentation and is used to transfer the native
pointwise vector-space operations back to the local-predicate section type. -/
theorem holomorphicPFormSectionTotal_eq
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U) :
    s.1 = fun x : U.unop =>
      TotalSpace.mk' (HolomorphicPFormModelFiberData (E := E) p) x.1
        (holomorphicPFormSectionValueData (X := X) I p U s x) := by
  funext x
  apply TotalSpace.ext
  · exact congrFun s.2.2 x
  · simp [holomorphicPFormSectionValueData]

/-- Analytic regularity of the dependent fibre-valued section underlying a
section of `Ω_X^p`. -/
theorem holomorphicPFormSection_contMDiff
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U) :
    ContMDiff I
      (I.prod 𝓘(ℂ, HolomorphicPFormModelFiberData (E := E) p)) ω
      (fun x : U.unop =>
        TotalSpace.mk' (HolomorphicPFormModelFiberData (E := E) p) x.1
          (holomorphicPFormSectionValueData (X := X) I p U s x)) := by
  rw [← holomorphicPFormSectionTotal_eq (X := X) I p U s]
  exact s.2.1

/-- Zero holomorphic `p`-form section on an open set. -/
noncomputable def holomorphicPFormZeroSectionData
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ) :
    (holomorphicPFormSheafData (X := X) I p).presheaf.obj U :=
  ⟨fun x => TotalSpace.mk'
      (HolomorphicPFormModelFiberData (E := E) p) x.1 0,
    by
      constructor
      · exact (contMDiff_zeroSection ℂ
          (HolomorphicPFormFiberData (X := X) I p)).comp contMDiff_subtype_val
      · rfl⟩

/-- Pointwise sum of two holomorphic `p`-form sections. -/
noncomputable def holomorphicPFormAddSectionData
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s t : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U) :
    (holomorphicPFormSheafData (X := X) I p).presheaf.obj U :=
  ⟨fun x => TotalSpace.mk'
      (HolomorphicPFormModelFiberData (E := E) p) x.1
      (holomorphicPFormSectionValueData (X := X) I p U s x +
        holomorphicPFormSectionValueData (X := X) I p U t x),
    by
      constructor
      · intro x0
        change ContMDiffAt I
          (I.prod 𝓘(ℂ, HolomorphicPFormModelFiberData (E := E) p)) ω
          (fun x : U.unop => TotalSpace.mk'
            (HolomorphicPFormModelFiberData (E := E) p) x.1
            (holomorphicPFormSectionValueData (X := X) I p U s x +
              holomorphicPFormSectionValueData (X := X) I p U t x)) x0
        rw [contMDiffAt_totalSpace]
        constructor
        · exact contMDiff_subtype_val.contMDiffAt
        · have hs := (holomorphicPFormSection_contMDiff (X := X) I p U s) x0
          have ht := (holomorphicPFormSection_contMDiff (X := X) I p U t) x0
          rw [contMDiffAt_totalSpace] at hs ht
          let e := trivializationAt
            (HolomorphicPFormModelFiberData (E := E) p)
            (HolomorphicPFormFiberData (X := X) I p) x0.1
          have hs' : ContMDiffAt I 𝓘(ℂ, HolomorphicPFormModelFiberData (E := E) p) ω
              (fun x => (e ⟨x.1, holomorphicPFormSectionValueData (X := X) I p U s x⟩).2) x0 :=
            hs.2
          have ht' : ContMDiffAt I 𝓘(ℂ, HolomorphicPFormModelFiberData (E := E) p) ω
              (fun x => (e ⟨x.1, holomorphicPFormSectionValueData (X := X) I p U t x⟩).2) x0 :=
            ht.2
          refine (hs'.add ht').congr_of_eventuallyEq ?_
          filter_upwards [continuousAt_subtype_val.preimage_mem_nhds
            (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x0.1))]
            with x hx
          exact (e.linear ℂ hx).map_add _ _
      · rfl⟩

/-- Pointwise additive inverse of a holomorphic `p`-form section. -/
noncomputable def holomorphicPFormNegSectionData
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U) :
    (holomorphicPFormSheafData (X := X) I p).presheaf.obj U :=
  ⟨fun x => TotalSpace.mk'
      (HolomorphicPFormModelFiberData (E := E) p) x.1
      (-holomorphicPFormSectionValueData (X := X) I p U s x),
    by
      constructor
      · intro x0
        change ContMDiffAt I
          (I.prod 𝓘(ℂ, HolomorphicPFormModelFiberData (E := E) p)) ω
          (fun x : U.unop => TotalSpace.mk'
            (HolomorphicPFormModelFiberData (E := E) p) x.1
            (-holomorphicPFormSectionValueData (X := X) I p U s x)) x0
        rw [contMDiffAt_totalSpace]
        constructor
        · exact contMDiff_subtype_val.contMDiffAt
        · have hs := (holomorphicPFormSection_contMDiff (X := X) I p U s) x0
          rw [contMDiffAt_totalSpace] at hs
          let e := trivializationAt
            (HolomorphicPFormModelFiberData (E := E) p)
            (HolomorphicPFormFiberData (X := X) I p) x0.1
          have hs' : ContMDiffAt I 𝓘(ℂ, HolomorphicPFormModelFiberData (E := E) p) ω
              (fun x => (e ⟨x.1, holomorphicPFormSectionValueData (X := X) I p U s x⟩).2) x0 :=
            hs.2
          refine hs'.neg.congr_of_eventuallyEq ?_
          filter_upwards [continuousAt_subtype_val.preimage_mem_nhds
            (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x0.1))]
            with x hx
          exact (e.linear ℂ hx).map_neg _
      · rfl⟩

/-- Pointwise constant complex scalar multiplication of a holomorphic
`p`-form section. -/
noncomputable def holomorphicPFormSMulSectionData
    (p : ℕ) (c : ℂ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U) :
    (holomorphicPFormSheafData (X := X) I p).presheaf.obj U :=
  ⟨fun x => TotalSpace.mk'
      (HolomorphicPFormModelFiberData (E := E) p) x.1
      (c • holomorphicPFormSectionValueData (X := X) I p U s x),
    by
      constructor
      · intro x0
        change ContMDiffAt I
          (I.prod 𝓘(ℂ, HolomorphicPFormModelFiberData (E := E) p)) ω
          (fun x : U.unop => TotalSpace.mk'
            (HolomorphicPFormModelFiberData (E := E) p) x.1
            (c • holomorphicPFormSectionValueData (X := X) I p U s x)) x0
        rw [contMDiffAt_totalSpace]
        constructor
        · exact contMDiff_subtype_val.contMDiffAt
        · have hs := (holomorphicPFormSection_contMDiff (X := X) I p U s) x0
          rw [contMDiffAt_totalSpace] at hs
          let e := trivializationAt
            (HolomorphicPFormModelFiberData (E := E) p)
            (HolomorphicPFormFiberData (X := X) I p) x0.1
          have hs' : ContMDiffAt I 𝓘(ℂ, HolomorphicPFormModelFiberData (E := E) p) ω
              (fun x => (e ⟨x.1, holomorphicPFormSectionValueData (X := X) I p U s x⟩).2) x0 :=
            hs.2
          have hc : ContMDiffAt I 𝓘(ℂ, ℂ) ω (fun _ : U.unop => c) x0 := contMDiffAt_const
          refine (hc.smul hs').congr_of_eventuallyEq ?_
          filter_upwards [continuousAt_subtype_val.preimage_mem_nhds
            (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x0.1))]
            with x hx
          exact (e.linear ℂ hx).map_smul c _
      · rfl⟩

/-- Fibre-value evaluation is injective on holomorphic-form sections. -/
theorem holomorphicPFormSectionValue_injective
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ) :
    Function.Injective (fun s : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U =>
      fun x : U.unop => holomorphicPFormSectionValueData (X := X) I p U s x) := by
  intro s t h
  apply Subtype.ext
  rw [holomorphicPFormSectionTotal_eq (X := X) I p U s,
    holomorphicPFormSectionTotal_eq (X := X) I p U t]
  funext x
  have hx := congrFun h x
  change holomorphicPFormSectionValueData (X := X) I p U s x =
    holomorphicPFormSectionValueData (X := X) I p U t x at hx
  rw [hx]

noncomputable instance holomorphicPFormSectionZero (p : ℕ)
    (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ) :
    Zero ((holomorphicPFormSheafData (X := X) I p).presheaf.obj U) :=
  ⟨holomorphicPFormZeroSectionData (X := X) I p U⟩

noncomputable instance holomorphicPFormSectionAdd (p : ℕ)
    (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ) :
    Add ((holomorphicPFormSheafData (X := X) I p).presheaf.obj U) :=
  ⟨holomorphicPFormAddSectionData (X := X) I p U⟩

noncomputable instance holomorphicPFormSectionNeg (p : ℕ)
    (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ) :
    Neg ((holomorphicPFormSheafData (X := X) I p).presheaf.obj U) :=
  ⟨holomorphicPFormNegSectionData (X := X) I p U⟩

noncomputable instance holomorphicPFormSectionSub (p : ℕ)
    (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ) :
    Sub ((holomorphicPFormSheafData (X := X) I p).presheaf.obj U) :=
  ⟨fun s t => s + -t⟩

noncomputable instance holomorphicPFormSectionNSMul (p : ℕ)
    (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ) :
    SMul ℕ ((holomorphicPFormSheafData (X := X) I p).presheaf.obj U) :=
  ⟨nsmulRec⟩

noncomputable instance holomorphicPFormSectionZSMul (p : ℕ)
    (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ) :
    SMul ℤ ((holomorphicPFormSheafData (X := X) I p).presheaf.obj U) :=
  ⟨zsmulRec⟩

@[simp] theorem holomorphicPFormSectionValue_zero
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ) (x : U.unop) :
    holomorphicPFormSectionValueData (X := X) I p U
      (0 : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U) x = 0 := rfl

@[simp] theorem holomorphicPFormSectionValue_add
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s t : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U) (x : U.unop) :
    holomorphicPFormSectionValueData (X := X) I p U (s + t) x =
      holomorphicPFormSectionValueData (X := X) I p U s x +
        holomorphicPFormSectionValueData (X := X) I p U t x := rfl

@[simp] theorem holomorphicPFormSectionValue_neg
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U) (x : U.unop) :
    holomorphicPFormSectionValueData (X := X) I p U (-s) x =
      -holomorphicPFormSectionValueData (X := X) I p U s x := rfl

@[simp] theorem holomorphicPFormSectionValue_sub
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s t : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U) (x : U.unop) :
    holomorphicPFormSectionValueData (X := X) I p U (s - t) x =
      holomorphicPFormSectionValueData (X := X) I p U s x -
        holomorphicPFormSectionValueData (X := X) I p U t x := rfl

@[simp] theorem holomorphicPFormSectionValue_nsmul
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U)
    (n : ℕ) (x : U.unop) :
    holomorphicPFormSectionValueData (X := X) I p U (n • s) x =
      n • holomorphicPFormSectionValueData (X := X) I p U s x := by
  induction n with
  | zero =>
      simp only [zero_nsmul]
      exact holomorphicPFormSectionValue_zero (X := X) I p U x
  | succ n ih =>
      change holomorphicPFormSectionValueData (X := X) I p U (n • s + s) x = _
      rw [holomorphicPFormSectionValue_add, ih, succ_nsmul]

@[simp] theorem holomorphicPFormSectionValue_zsmul
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U)
    (z : ℤ) (x : U.unop) :
    holomorphicPFormSectionValueData (X := X) I p U (z • s) x =
      z • holomorphicPFormSectionValueData (X := X) I p U s x := by
  rcases z with n | n
  · refine (holomorphicPFormSectionValue_nsmul (X := X) I p U s n x).trans ?_
    simp only [Int.ofNat_eq_natCast, natCast_zsmul]
  · change holomorphicPFormSectionValueData (X := X) I p U (-((n + 1) • s)) x = _
    rw [holomorphicPFormSectionValue_neg, holomorphicPFormSectionValue_nsmul]
    simp only [negSucc_zsmul]

noncomputable instance holomorphicPFormSectionAddCommGroup (p : ℕ)
    (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ) :
    AddCommGroup ((holomorphicPFormSheafData (X := X) I p).presheaf.obj U) :=
  (holomorphicPFormSectionValue_injective (X := X) I p U).addCommGroup
    (fun s x => holomorphicPFormSectionValueData (X := X) I p U s x)
    (by funext x; exact holomorphicPFormSectionValue_zero (X := X) I p U x)
    (fun s t => by funext x; exact holomorphicPFormSectionValue_add (X := X) I p U s t x)
    (fun s => by funext x; exact holomorphicPFormSectionValue_neg (X := X) I p U s x)
    (fun s t => by funext x; exact holomorphicPFormSectionValue_sub (X := X) I p U s t x)
    (fun s n => by funext x; exact holomorphicPFormSectionValue_nsmul (X := X) I p U s n x)
    (fun s z => by funext x; exact holomorphicPFormSectionValue_zsmul (X := X) I p U s z x)

noncomputable instance holomorphicPFormSectionSMul (p : ℕ)
    (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ) :
    SMul ℂ ((holomorphicPFormSheafData (X := X) I p).presheaf.obj U) :=
  ⟨fun c s => holomorphicPFormSMulSectionData (X := X) I p c U s⟩

@[simp] theorem holomorphicPFormSectionValue_smul
    (p : ℕ) (c : ℂ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)
    (s : (holomorphicPFormSheafData (X := X) I p).presheaf.obj U) (x : U.unop) :
    holomorphicPFormSectionValueData (X := X) I p U (c • s) x =
      c • holomorphicPFormSectionValueData (X := X) I p U s x := rfl

noncomputable def holomorphicPFormSectionValueAddHom
    (p : ℕ) (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ) :
    (holomorphicPFormSheafData (X := X) I p).presheaf.obj U →+
      ((x : U.unop) → HolomorphicPFormFiberData (X := X) I p x.1) where
  toFun s x := holomorphicPFormSectionValueData (X := X) I p U s x
  map_zero' := by funext x; exact holomorphicPFormSectionValue_zero (X := X) I p U x
  map_add' s t := by funext x; exact holomorphicPFormSectionValue_add (X := X) I p U s t x

noncomputable instance holomorphicPFormSectionModule (p : ℕ)
    (U : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ) :
    Module ℂ ((holomorphicPFormSheafData (X := X) I p).presheaf.obj U) :=
  (holomorphicPFormSectionValue_injective (X := X) I p U).module ℂ
    (holomorphicPFormSectionValueAddHom (X := X) I p U)
    (fun c s => by funext x; exact holomorphicPFormSectionValue_smul (X := X) I p c U s x)

/-- Restriction of holomorphic forms is complex-linear. -/
noncomputable def holomorphicPFormRestrictionLinearMap
    (p : ℕ) {U V : (TopologicalSpace.Opens (TopCat.of X))ᵒᵖ} (h : U ⟶ V) :
    (holomorphicPFormSheafData (X := X) I p).presheaf.obj U →ₗ[ℂ]
      (holomorphicPFormSheafData (X := X) I p).presheaf.obj V where
  toFun := (holomorphicPFormSheafData (X := X) I p).presheaf.map h
  map_add' s t := by
    apply holomorphicPFormSectionValue_injective (X := X) I p V
    funext x
    rfl
  map_smul' c s := by
    apply holomorphicPFormSectionValue_injective (X := X) I p V
    funext x
    rfl

/-- Presheaf of complex vector spaces underlying the holomorphic `p`-form
sheaf.  The object types are definitionally the same section types as
`holomorphicPFormSheafData`. -/
noncomputable def holomorphicPFormPresheafModuleData (p : ℕ) :
    TopCat.Presheaf (ModuleCat.{u} ℂ) (TopCat.of X) where
  obj U := ModuleCat.of ℂ ((holomorphicPFormSheafData (X := X) I p).presheaf.obj U)
  map h := ModuleCat.ofHom (holomorphicPFormRestrictionLinearMap (X := X) I p h)
  map_id U := by ext s; rfl
  map_comp f g := by ext s; rfl

/-- Canonical complex-vector-space-valued sheaf `Ω_X^p`.

Sheafhood is reflected by the forgetful functor to types, where the presheaf
is definitionally the already-realized `holomorphicPFormSheafData`. -/
noncomputable def holomorphicPFormSheafModuleSmoothData (p : ℕ) :
    TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of X) where
  obj := holomorphicPFormPresheafModuleData (X := X) I p
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget (ModuleCat.{u} ℂ))]
    exact (holomorphicPFormSheafData (X := X) I p).property

end SmoothModuleSheaf

/-- Source-facing complex-vector-space-valued sheaf `Ω_X^p` on an analytic
complex manifold.  Analytic regularity canonically supplies the smooth
regularity needed by the vector-bundle operation implementation. -/
noncomputable def holomorphicPFormSheafModuleData (p : ℕ) :
    TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of X) := by
  letI : IsManifold I ∞ X := IsManifold.of_le le_top
  exact holomorphicPFormSheafModuleSmoothData (X := X) I p

/-- The additive sheaf underlying the complex-vector-space-valued
holomorphic `p`-form sheaf.  This is the coefficient object consumed by
Mathlib's native sheaf-cohomology functor. -/
noncomputable def holomorphicPFormAdditiveSheafData (p : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X) := by
  letI : IsManifold I ∞ X := IsManifold.of_le le_top
  exact (CategoryTheory.sheafCompose
    (Opens.grothendieckTopology (TopCat.of X))
    (CategoryTheory.forget₂ (ModuleCat.{u} ℂ) AddCommGrpCat.{u})).obj
      (holomorphicPFormSheafModuleSmoothData (X := X) I p)

/-- Peters--Sterk's Hodge-cohomology group carrier
`H^{p,q}(X) = H^q(X, Ω_X^p)`.

The complex vector-space structure induced from the coefficient sheaf is a
separate categorical layer; this declaration records the actual native
sheaf-cohomology group rather than a proxy. -/
noncomputable def hodgeCohomologyGroupData
    [Abelian (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X))]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{u}]
    (hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X)))
    (p q : ℕ) : Type (u + 1) := by
  exact @CategoryTheory.Abelian.Ext _ _ _ hExt
    ((CategoryTheory.constantSheaf
      (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ)))
    (holomorphicPFormAdditiveSheafData (X := X) I p) q

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

/-- Global sections of a complex-vector-space-valued sheaf on a complex
manifold.  This is evaluation on the top open set. -/
abbrev holomorphicModuleSheafGlobalSectionsData
    (F : TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of X)) :=
  F.presheaf.obj (.op ⊤)

/-- Numerical dimension of global sections of a supplied complex-linear
sheaf.  For the actual pluricanonical sheaf this is Peters--Sterk's
plurigenus; finite-dimensionality is a separate result. -/
noncomputable def plurigenusOfSheafData
    (F : TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of X)) : ℕ :=
  Module.finrank ℂ (holomorphicModuleSheafGlobalSectionsData (X := X) F)

end LeanCategories.Geometry

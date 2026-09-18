/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CEResolution
public import LeanCategories.Homological.RightCEResolution
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Invariants

/-!
# Group hyperhomology and hypercohomology

Weibel, *An Introduction to Homological Algebra* (1994), Definition 6.1.15,
pp. 160--166 (FC05-C06-U017).

Group hyperhomology is the left hyper-derived functor of coinvariants on a
chain complex of `G`-modules.  Group hypercohomology is the right hyper-derived
functor of invariants on a cochain complex of `G`-modules.

The resolution-independence and spectral-sequence comparisons are result-level
content and are not asserted here.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory

universe u

variable (G : Type u) [Group G]

/-- Weibel's group hyperhomology `𝕳_n(G;A_*)`, computed from a chosen left
C--E resolution of a chain complex of integral `G`-modules. -/
noncomputable def groupHyperhomology
  {A : ChainComplex (Rep.{u} ℤ G) ℕ} (P : LeftCEResolution A) (n : ℕ) :
    ModuleCat ℤ :=
  let F := Rep.coinvariantsFunctor ℤ G
  let K : ChainComplex (ChainComplex (ModuleCat ℤ) ℕ) ℕ :=
    let H := F.mapHomologicalComplex (ComplexShape.down ℕ)
    (H.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.P
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).obj
    (HomologicalComplex₂.total K (ComplexShape.down ℕ))

/-- Weibel's group hypercohomology `𝕳^n(G;A^*)`, computed from a chosen right
C--E resolution of a cochain complex of integral `G`-modules. -/
noncomputable def groupHypercohomology
  {A : CochainComplex (Rep.{u} ℤ G) ℕ} (I : RightCEResolution A) (n : ℕ) :
    ModuleCat ℤ :=
  let F := Rep.invariantsFunctor ℤ G
  let K₀ : CochainComplex (CochainComplex (ModuleCat ℤ) ℕ) ℕ :=
    let H := F.mapHomologicalComplex (ComplexShape.up ℕ)
    (H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.I
  let innerExtend := ComplexShape.embeddingUpNat.extendFunctor (ModuleCat ℤ)
  let K₁ : CochainComplex (CochainComplex (ModuleCat ℤ) ℤ) ℕ :=
    (innerExtend.mapHomologicalComplex (ComplexShape.up ℕ)).obj K₀
  let K : CochainComplex (CochainComplex (ModuleCat ℤ) ℤ) ℤ :=
    (ComplexShape.embeddingUpNat.extendFunctor (CochainComplex (ModuleCat ℤ) ℤ)).obj K₁
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℤ) (n : ℤ)).obj
    (HomologicalComplex₂.total K (ComplexShape.up ℤ))

end LeanCategories.Homological

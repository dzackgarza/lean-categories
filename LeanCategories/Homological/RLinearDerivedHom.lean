/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DerivedHom
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# The `R`-linear refinement of derived Hom

Weibel, *An Introduction to Homological Algebra* (1994), §10.7.1,
pp. 398--401 (FC05-C10-U085).

For a commutative ring `R`, the ordinary total Hom complex computing
`RHom_R(A,B)` carries its canonical `R`-module structure.  Hence the derived
Hom object may be regarded in `D(R)`, refining its underlying object in
`D(Ab)`.  The canonical owner below retains the `R`-module structure on
Mathlib's cochain modules and applies the same internally chosen fibrant
replacement used by `rHom`.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory
open CochainComplex.HomComplex

universe u


variable (R : Type u) [CommRing R]

/-- The `R`-linear total Hom complex of two cochain complexes.

This is the data-level part of TauCeti's `linearHomComplex`: Mathlib already supplies the
`R`-linear signed differential and its shape/square-zero identities, so this declaration only
retains the module structure that `CochainComplex.HomComplex` forgets.

Reference: `TauCeti/Algebra/Homology/LinearHomComplex/Basic.lean::TauCeti.linearHomComplex`. -/
def linearHomComplex
    (A B : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ where
  X n := ModuleCat.of R (Cochain A B n)
  d n m := ModuleCat.ofHom (δ_hom R A B n m)
  shape n m hnm := ModuleCat.hom_ext (LinearMap.ext fun z => δ_shape n m hnm z)
  d_comp_d' n m p _ _ := ModuleCat.hom_ext (LinearMap.ext fun z => δ_δ n m p z)

/-- Weibel's `RHom_R(A,B)` as an object of `D(R)`.

The bounded-below representative of `B` and its fibrant replacement are chosen internally.
Forgetting the resulting module complex recovers the ordinary total-Hom construction; the
comparison isomorphism and all functoriality statements are result-layer material.

Source: Weibel, §10.7.1, pp. 398--401 (FC05-C10-U085). -/
noncomputable def rHomR [HasDerivedCategory (ModuleCat.{u} R)]
    (A : CochainComplex (ModuleCat.{u} R) ℤ)
    (B : DerivedCategory.Plus (ModuleCat.{u} R)) :
    DerivedCategory (ModuleCat.{u} R) := by
  letI : EnoughInjectives (ModuleCat.{u} R) := ModuleCat.enoughInjectives R
  exact DerivedCategory.Q.obj
    (linearHomComplex R A (rHomInjectiveRepresentative B).obj)

/-- Auxiliary caller-specified `R`-linear lift of an explicit total-Hom representative.

Forgetting the `R`-module structure degreewise recovers the underlying
abelian-group Hom complex used by `rHomViaInjectiveReplacement`.

This structure is retained for downstream comparison constructions; the canonical owner of
FC05-C10-U085 is `rHomR`. -/
structure RLinearRHomRefinement
    (A : CochainComplex (ModuleCat.{u} R) ℤ)
    (B : CochainComplex.Plus (ModuleCat.{u} R))
    (I : RHomInjectiveReplacement B) where
  /-- The `R`-linear total Hom complex. -/
  complex : CochainComplex (ModuleCat.{u} R) ℤ
  /-- Forgetting scalars recovers the underlying derived-Hom representative. -/
  forgetIso :
    (((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj complex) ≅
      rHomViaInjectiveReplacement A B I

/-- The raw `R`-linear Hom complex attached to an explicitly supplied refinement. -/
def rHomRViaInjectiveReplacement
    (A : CochainComplex (ModuleCat.{u} R) ℤ)
    (B : CochainComplex.Plus (ModuleCat.{u} R))
    (I : RHomInjectiveReplacement B)
    (H : RLinearRHomRefinement R A B I) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  H.complex

end LeanCategories.Homological

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DerivedHom
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The `R`-linear refinement of derived Hom

Weibel, *An Introduction to Homological Algebra* (1994), §10.7.1,
pp. 398--401 (FC05-C10-U085).

For a commutative ring `R`, the ordinary total Hom complex computing
`RHom_R(A,B)` carries its canonical `R`-module structure.  Hence the derived
Hom object may be regarded in `D(R)`, refining its underlying object in
`D(Ab)`.  The structure below records exactly that lift on a chosen
K-injective representative.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory

universe u


variable (R : Type u) [CommRing R]

/-- An `R`-linear lift of the total Hom complex representing `RHom_R(A,B)`.

Forgetting the `R`-module structure degreewise recovers the underlying
abelian-group Hom complex used by `rHomViaInjectiveReplacement`.

Source: Weibel, §10.7.1, pp. 398--401 (FC05-C10-U085). -/
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

/-- `RHom_R(A,B)` regarded as an `R`-linear complex once a refinement has
been chosen.

Source: Weibel, §10.7.1, pp. 398--401 (FC05-C10-U085). -/
def rHomRViaInjectiveReplacement
    (A : CochainComplex (ModuleCat.{u} R) ℤ)
    (B : CochainComplex.Plus (ModuleCat.{u} R))
    (I : RHomInjectiveReplacement B)
    (H : RLinearRHomRefinement R A B I) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  H.complex

end LeanCategories.Homological

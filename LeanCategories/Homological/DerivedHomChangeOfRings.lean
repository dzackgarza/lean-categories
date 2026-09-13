/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.RLinearDerivedHom
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Change of rings for derived Hom

Weibel, *An Introduction to Homological Algebra* (1994), §10.7.1,
pp. 398--401 (FC05-C10-U086).

For a ring homomorphism `f : R → S`, restriction of scalars gives the natural
comparison

`f_* RHom_S(A,B) → RHom_R(f_*A,f_*B)`.

The map is supplied by the universal property of the right derived functor.
This file records its source and target at the `R`-linear representative level;
properties such as being an isomorphism under stronger hypotheses are later
result-layer statements.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Restriction of scalars on integer cochain complexes. -/
def restrictScalarsCochain (f : R →+* S) :
    CochainComplex (ModuleCat.{u} S) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  (ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Restriction of scalars on bounded-below cochain complexes. -/
def restrictScalarsCochainPlus (f : R →+* S) :
    CochainComplex.Plus (ModuleCat.{u} S) ⥤
      CochainComplex.Plus (ModuleCat.{u} R) :=
  (ModuleCat.restrictScalars f).mapCochainComplexPlus

/-- Representative-level data for Weibel's natural change-of-rings map
`f_*RHom_S(A,B) → RHom_R(f_*A,f_*B)`.

The source and target refinements specify the chosen K-injective models; the
comparison morphism is the map furnished by the right-derived universal
property.

Source: Weibel, §10.7.1, pp. 398--401 (FC05-C10-U086). -/
structure RHomChangeOfRingsRealization
    (f : R →+* S)
    (A : CochainComplex (ModuleCat.{u} S) ℤ)
    (B : CochainComplex.Plus (ModuleCat.{u} S))
    (IS : RHomInjectiveReplacement B)
    (HS : RLinearRHomRefinement S A B IS)
    (IR : RHomInjectiveReplacement ((restrictScalarsCochainPlus f).obj B))
    (HR : RLinearRHomRefinement R
      ((restrictScalarsCochain f).obj A)
      ((restrictScalarsCochainPlus f).obj B) IR) where
  /-- `f_*RHom_S(A,B) → RHom_R(f_*A,f_*B)`. -/
  map : (restrictScalarsCochain f).obj HS.complex ⟶ HR.complex

/-- The change-of-rings comparison map for chosen `RHom` representatives.

Source: Weibel, §10.7.1, pp. 398--401 (FC05-C10-U086). -/
def rHomChangeOfRingsMap
    (f : R →+* S)
    (A : CochainComplex (ModuleCat.{u} S) ℤ)
    (B : CochainComplex.Plus (ModuleCat.{u} S))
    (IS : RHomInjectiveReplacement B)
    (HS : RLinearRHomRefinement S A B IS)
    (IR : RHomInjectiveReplacement ((restrictScalarsCochainPlus f).obj B))
    (HR : RLinearRHomRefinement R
      ((restrictScalarsCochain f).obj A)
      ((restrictScalarsCochainPlus f).obj B) IR)
    (H : RHomChangeOfRingsRealization f A B IS HS IR HR) :
    (restrictScalarsCochain f).obj HS.complex ⟶ HR.complex :=
  H.map

end LeanCategories.Homological

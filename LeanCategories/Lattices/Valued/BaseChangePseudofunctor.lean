/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.BaseChangeCoherence
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import LeanCategories.ForMathlib.GrothendieckCocartesian

@[expose] public section

/-!
# Bilinear forms as a cocartesian fibration over commutative rings

FOUNDATIONS §15.5–15.6: bilinear forms are functorial in the value module (change of
values, the cocartesian transport of `BilWFormCat R` over `ModuleCat R`, `Total.lean`)
and in the ring (base change, `BaseChange.lean`). This file assembles base change into
the pseudofunctor `CommRingCat ⥤ Cat`, `R ↦ BilWFormCat R`, from the existing functors
`baseChangeBilWForm` and their identity and composition isomorphisms; the total
category of forms over all rings is its Grothendieck construction, a cocartesian
fibration over `CommRingCat` (specs/registry-denotation-audit.md §4).
-/

open CategoryTheory

noncomputable section

namespace LeanCategories.Lattices.Valued

universe u

open LeanCategories.Modules.Bilinear.Valued

/-- Base change of forms along a morphism of commutative rings. -/
def baseChangeAlong {R S : CommRingCat.{u}} (f : R ⟶ S) :
    BilWFormCat R ⥤ BilWFormCat S :=
  letI := f.hom.toAlgebra
  baseChangeBilWForm R S

/-- Base change along the identity is the identity, up to the existing isomorphism. -/
def baseChangeAlongId (R : CommRingCat.{u}) : baseChangeAlong (𝟙 R) ≅ 𝟭 (BilWFormCat R) :=
  baseChangeBilWFormIdentityIso R

/-- Base change along a composite is the composite of base changes, up to the existing
isomorphism. -/
def baseChangeAlongComp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    baseChangeAlong (f ≫ g) ≅ baseChangeAlong f ⋙ baseChangeAlong g :=
  letI := f.hom.toAlgebra
  letI := g.hom.toAlgebra
  letI := (f ≫ g).hom.toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  baseChangeBilWFormCompositionIso R S T

/-- Base change of bilinear forms as a pseudofunctor on commutative rings. -/
def bilinBaseChangePseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat.{u, u + 1} := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of (BilWFormCat R))
    (fun f ↦ (baseChangeAlong f).toCatHom)
    (fun R ↦ Cat.Hom.isoMk (baseChangeAlongId R))
    (fun f g ↦ Cat.Hom.isoMk (baseChangeAlongComp f g)) ?_ ?_ ?_
  · intro R S T U f g h
    ext1
    let _ := f.hom.toAlgebra
    let _ := g.hom.toAlgebra
    let _ := h.hom.toAlgebra
    let _ := (f ≫ g).hom.toAlgebra
    let _ := (g ≫ h).hom.toAlgebra
    let _ := (f ≫ g ≫ h).hom.toAlgebra
    have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower R T U := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower S T U := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact baseChangeBilWForm_assoc R S T U
  · intro R S f
    ext1
    let _ := f.hom.toAlgebra
    exact baseChangeBilWForm_id_comp R S
  · intro R S f
    ext1
    let _ := f.hom.toAlgebra
    exact baseChangeBilWForm_comp_id R S

open Pseudofunctor.Grothendieck in
/-- Bilinear forms over all commutative rings and value modules: the Grothendieck
construction of base change (FOUNDATIONS §15.2, §15.5–15.6). Its fibre over `R` is
`BilWFormCat R`. -/
abbrev BilinFormsOverRings : Type (u + 1) := ∫ bilinBaseChangePseudofunctor.{u}

/-- The projection of forms to their commutative ring. -/
abbrev BilinFormsOverRings.ring : BilinFormsOverRings.{u} ⥤ CommRingCat.{u} :=
  Pseudofunctor.Grothendieck.forget _

/-- Base change is the cocartesian transport: the canonical lift of `f : R ⟶ S` at a form over
`R` is strongly cocartesian for the projection to rings. -/
theorem BilinFormsOverRings.isStronglyCocartesian_baseChange {R S : CommRingCat.{u}}
    (X : BilWFormCat R) (f : R ⟶ S) :
    Functor.IsStronglyCocartesian BilinFormsOverRings.ring f
      (Pseudofunctor.Grothendieck.cocartesianLift (F := bilinBaseChangePseudofunctor) X f) :=
  Pseudofunctor.Grothendieck.isStronglyCocartesian_cocartesianLift
    (F := bilinBaseChangePseudofunctor) (R := R) (S := S) X f

end LeanCategories.Lattices.Valued

end

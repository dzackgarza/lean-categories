/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Quadratic.Valued.BaseChange
public import LeanCategories.Lattices.Valued.BaseChangeCoherence
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import LeanCategories.ForMathlib.GrothendieckCocartesian

@[expose] public section

/-!
# Quadratic forms as a cocartesian fibration over commutative rings

Base change of quadratic forms (`BaseChange.lean`, characteristic-free: no hypothesis on `2`) with
its identity and composition isomorphisms satisfies the associativity and unit laws of a
pseudofunctor `CommRingCat ⥤ Cat`, `R ↦ QuadWFormCat R`; the laws are those of the underlying
modules, checked on pure tensors exactly as for bilinear forms (`BaseChangeCoherence.lean`, whose
module-level lemmas are reused). The total category of quadratic forms over all rings is its
Grothendieck construction, a cocartesian fibration over `CommRingCat` (FOUNDATIONS §15.6).
-/

open CategoryTheory TensorProduct

noncomputable section

namespace LeanCategories.Modules.Quadratic.Valued

universe u

section Components

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

@[simp]
theorem valueMap_baseChangeQuadWForm_map {X Y : QuadWFormCat R} (g : X ⟶ Y) :
    QuadWFormCat.valueMap ((baseChangeQuadWForm R S).map g) =
      ModuleCat.ofHom (LinearMap.baseChange S (QuadWFormCat.valueMap g).hom) :=
  rfl

@[simp]
theorem carrierMap_baseChangeQuadWForm_map {X Y : QuadWFormCat R} (g : X ⟶ Y) :
    QuadWFormCat.carrierMap ((baseChangeQuadWForm R S).map g) =
      ModuleCat.ofHom (LinearMap.baseChange S (QuadWFormCat.carrierMap g).hom) :=
  rfl

@[simp]
theorem valueMap_compositionIso_hom_app (X : QuadWFormCat R) :
    QuadWFormCat.valueMap ((baseChangeQuadWFormCompositionIso R S T).hom.app X) =
      ModuleCat.ofHom
        (AlgebraTensorModule.cancelBaseChange R S T T X.value).symm.toLinearMap :=
  rfl

@[simp]
theorem carrierMap_compositionIso_hom_app (X : QuadWFormCat R) :
    QuadWFormCat.carrierMap ((baseChangeQuadWFormCompositionIso R S T).hom.app X) =
      ModuleCat.ofHom
        (AlgebraTensorModule.cancelBaseChange R S T T X.carrier).symm.toLinearMap :=
  rfl

@[simp]
theorem valueMap_compositionIso_inv_app (X : QuadWFormCat R) :
    QuadWFormCat.valueMap ((baseChangeQuadWFormCompositionIso R S T).inv.app X) =
      ModuleCat.ofHom
        (AlgebraTensorModule.cancelBaseChange R S T T X.value).toLinearMap :=
  rfl

@[simp]
theorem carrierMap_compositionIso_inv_app (X : QuadWFormCat R) :
    QuadWFormCat.carrierMap ((baseChangeQuadWFormCompositionIso R S T).inv.app X) =
      ModuleCat.ofHom
        (AlgebraTensorModule.cancelBaseChange R S T T X.carrier).toLinearMap :=
  rfl

@[simp]
theorem valueMap_identityIso_hom_app (X : QuadWFormCat R) :
    QuadWFormCat.valueMap ((baseChangeQuadWFormIdentityIso R).hom.app X) =
      ModuleCat.ofHom (TensorProduct.lid R X.value).toLinearMap :=
  rfl

@[simp]
theorem carrierMap_identityIso_hom_app (X : QuadWFormCat R) :
    QuadWFormCat.carrierMap ((baseChangeQuadWFormIdentityIso R).hom.app X) =
      ModuleCat.ofHom (TensorProduct.lid R X.carrier).toLinearMap :=
  rfl

end Components

section Associativity

variable (R S T U : Type u) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
variable [Algebra R S] [Algebra S T] [Algebra T U] [Algebra R T] [Algebra S U] [Algebra R U]
variable [IsScalarTower R S T] [IsScalarTower R T U] [IsScalarTower S T U]
  [IsScalarTower R S U]

set_option backward.isDefEq.respectTransparency.types false in
/-- The associativity law of the composition isomorphisms of base change. -/
theorem baseChangeQuadWForm_assoc :
    (baseChangeQuadWFormCompositionIso R T U).hom ≫
      Functor.whiskerRight (baseChangeQuadWFormCompositionIso R S T).hom
        (baseChangeQuadWForm T U) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (baseChangeQuadWForm R S)
        (baseChangeQuadWFormCompositionIso S T U).inv ≫
      (baseChangeQuadWFormCompositionIso R S U).inv = 𝟙 _ := by
  ext X : 2
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, NatTrans.id_app, Category.id_comp]
  apply QuadWFormCat.hom_ext
  · exact ModuleCat.hom_ext (Lattices.Valued.cancelBaseChange_assoc R S T U X.value)
  · exact ModuleCat.hom_ext (Lattices.Valued.cancelBaseChange_assoc R S T U X.carrier)

end Associativity

section Unitors

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The left unit law of base change. -/
theorem baseChangeQuadWForm_id_comp :
    (baseChangeQuadWFormCompositionIso R R S).hom ≫
      Functor.whiskerRight (baseChangeQuadWFormIdentityIso R).hom (baseChangeQuadWForm R S) ≫
      (Functor.leftUnitor _).hom = 𝟙 _ := by
  ext X : 2
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    NatTrans.id_app]
  apply QuadWFormCat.hom_ext
  · exact ModuleCat.hom_ext (Lattices.Valued.cancelBaseChange_id_left R S X.value)
  · exact ModuleCat.hom_ext (Lattices.Valued.cancelBaseChange_id_left R S X.carrier)

/-- The right unit law of base change. -/
theorem baseChangeQuadWForm_comp_id :
    (baseChangeQuadWFormCompositionIso R S S).hom ≫
      Functor.whiskerLeft (baseChangeQuadWForm R S) (baseChangeQuadWFormIdentityIso S).hom ≫
      (Functor.rightUnitor _).hom = 𝟙 _ := by
  ext X : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    NatTrans.id_app]
  apply QuadWFormCat.hom_ext
  · exact ModuleCat.hom_ext (Lattices.Valued.cancelBaseChange_id_right R S X.value)
  · exact ModuleCat.hom_ext (Lattices.Valued.cancelBaseChange_id_right R S X.carrier)

end Unitors

/-- Base change of forms along a morphism of commutative rings. -/
def quadBaseChangeAlong {R S : CommRingCat.{u}} (f : R ⟶ S) :
    QuadWFormCat R ⥤ QuadWFormCat S :=
  letI := f.hom.toAlgebra
  baseChangeQuadWForm R S

/-- Base change along the identity is the identity, up to the existing isomorphism. -/
def quadBaseChangeAlongId (R : CommRingCat.{u}) : quadBaseChangeAlong (𝟙 R) ≅ 𝟭 (QuadWFormCat R) :=
  baseChangeQuadWFormIdentityIso R

/-- Base change along a composite is the composite of base changes, up to the existing
isomorphism. -/
def quadBaseChangeAlongComp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    quadBaseChangeAlong (f ≫ g) ≅ quadBaseChangeAlong f ⋙ quadBaseChangeAlong g :=
  letI := f.hom.toAlgebra
  letI := g.hom.toAlgebra
  letI := (f ≫ g).hom.toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  baseChangeQuadWFormCompositionIso R S T

/-- Base change of quadratic forms as a pseudofunctor on commutative rings. -/
@[simps! obj map mapId mapComp]
def quadBaseChangePseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat.{u, u + 1} := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of (QuadWFormCat R))
    (fun f ↦ (quadBaseChangeAlong f).toCatHom)
    (fun R ↦ Cat.Hom.isoMk (quadBaseChangeAlongId R))
    (fun f g ↦ Cat.Hom.isoMk (quadBaseChangeAlongComp f g)) ?_ ?_ ?_
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
    exact baseChangeQuadWForm_assoc R S T U
  · intro R S f
    ext1
    let _ := f.hom.toAlgebra
    exact baseChangeQuadWForm_id_comp R S
  · intro R S f
    ext1
    let _ := f.hom.toAlgebra
    exact baseChangeQuadWForm_comp_id R S

open Pseudofunctor.Grothendieck in
/-- Quadratic forms over all commutative rings and value modules: the Grothendieck construction of
base change (FOUNDATIONS §15.6). Its fibre over `R` is `QuadWFormCat R`. -/
abbrev QuadFormsOverRings : Type (u + 1) := ∫ quadBaseChangePseudofunctor.{u}

/-- The projection of quadratic forms to their commutative ring. -/
abbrev QuadFormsOverRings.ring : QuadFormsOverRings.{u} ⥤ CommRingCat.{u} :=
  Pseudofunctor.Grothendieck.forget _

/-- Base change is the cocartesian transport: the canonical lift of `f : R ⟶ S` at a form over
`R` is strongly cocartesian for the projection to rings. -/
theorem QuadFormsOverRings.isStronglyCocartesian_baseChange {R S : CommRingCat.{u}}
    (X : QuadWFormCat R) (f : R ⟶ S) :
    Functor.IsStronglyCocartesian QuadFormsOverRings.ring f
      (Pseudofunctor.Grothendieck.cocartesianLift (F := quadBaseChangePseudofunctor) X f) :=
  Pseudofunctor.Grothendieck.isStronglyCocartesian_cocartesianLift
    (F := quadBaseChangePseudofunctor) (R := R) (S := S) X f

end LeanCategories.Modules.Quadratic.Valued

end

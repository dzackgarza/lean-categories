/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.BaseChangePseudofunctor
public import LeanCategories.ForMathlib.GrothendieckMapCocartesian
public import LeanCategories.ForMathlib.LocallyDiscreteStrongTrans
public import LeanCategories.ForMathlib.GrothendieckFibers
public import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor

@[expose] public section

/-!
# Bilinear forms fibred over modules over rings

FOUNDATIONS Example 31.2c. The tower `Bil →p ∫Mod →q CommRing` of cocartesian fibrations:

* `q : ∫ moduleCatExtendScalarsPseudofunctor ⥤ CommRingCat` is the Grothendieck projection of
  extension of scalars; its fibre over `R` is `ModuleCat R`.
* `valueProjectionTrans : bilinBaseChangePseudofunctor ⟶ moduleCatExtendScalarsPseudofunctor`
  is the strong transformation with components the value projections
  `valueProjection R : BilWFormCat R ⥤ ModuleCat R`; base change of forms extends scalars on
  values on the nose, so its naturality isomorphisms are identities.
* `p := Pseudofunctor.Grothendieck.map valueProjectionTrans`, with `p ⋙ q` the projection of
  forms to rings (`Grothendieck.map_comp_forget`, by `rfl`). `p` is a cocartesian fibration by
  FOUNDATIONS Proposition 31.2b (`Pseudofunctor.Grothendieck.isCofibered_map`): each
  `valueProjection R` is one (change of values), and base change preserves
  value-cocartesian morphisms (`IsStronglyCocartesian.map_of_exists`, from the canonical lifts,
  whose base change has invertible carrier map).

The fibre of `p` over `(R, W)` is the category `BilinModuleCat R W` of `W`-valued bilinear
forms over `R`; the fibre of `p ⋙ q` over `R` is `BilWFormCat R`.
-/

open CategoryTheory

noncomputable section

namespace LeanCategories.Lattices.Valued

universe u

open LeanCategories.Modules.Bilinear.Valued

section ExtendScalars

variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)

set_option backward.isDefEq.respectTransparency false in
/-- The composition isomorphism of extension of scalars is the inverse cancellation
isomorphism. -/
theorem extendScalarsComp_hom_app_eq (W : ModuleCat.{u} R) :
    letI := f.hom.toAlgebra
    letI := g.hom.toAlgebra
    letI := (f ≫ g).hom.toAlgebra
    haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
    (ModuleCat.extendScalarsComp f.hom g.hom).hom.app W =
      ModuleCat.ofHom
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T W).symm.toLinearMap := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  erw [ModuleCat.extendScalarsComp_hom_app_one_tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identity comparison of extension of scalars is `lid`. -/
theorem extendScalarsId_hom_app_eq (W : ModuleCat.{u} R) :
    (ModuleCat.extendScalarsId R).hom.app W =
      ModuleCat.ofHom (TensorProduct.lid R W).toLinearMap := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  erw [ModuleCat.extendScalarsId_hom_app_one_tmul]

end ExtendScalars

/-- Value projection commutes with base change on the nose: the value module of the base
change of a form is the extension of scalars of its value module. -/
theorem baseChangeAlong_comp_valueProjection {R S : CommRingCat.{u}} (f : R ⟶ S) :
    baseChangeAlong f ⋙ valueProjection S =
      valueProjection R ⋙ ModuleCat.extendScalars f.hom :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The value projections form a strong transformation from base change of forms to extension
of scalars of modules. -/
def valueProjectionTrans : Pseudofunctor.StrongTrans bilinBaseChangePseudofunctor.{u}
    CommRingCat.moduleCatExtendScalarsPseudofunctor.{u} :=
  LocallyDiscrete.mkStrongTrans (fun R ↦ (valueProjection R).toCatHom)
    (fun f ↦ Cat.Hom.isoMk (eqToIso (baseChangeAlong_comp_valueProjection f)))
    (by
      intro R
      ext X : 3
      simp
      exact extendScalarsId_hom_app_eq _)
    (by
      intro R S T f g
      ext X : 3
      simp
      refine (extendScalarsComp_hom_app_eq f g _).trans ?_
      rfl)

open Pseudofunctor.Grothendieck in
/-- Modules over varying commutative rings, with extension of scalars as transport: the
cocartesian fibration of modules over `CommRingCat` (FOUNDATIONS §13.2). -/
abbrev ModulesOverRingsExt : Type (u + 1) :=
  ∫ CommRingCat.moduleCatExtendScalarsPseudofunctor.{u}

/-- The projection of modules to their commutative ring. -/
abbrev ModulesOverRingsExt.ring : ModulesOverRingsExt.{u} ⥤ CommRingCat.{u} :=
  Pseudofunctor.Grothendieck.forget _

/-- Module level: `T ⊗_R R → T ⊗_S (S ⊗_R R) → T ⊗_S S → T` is `T ⊗_R R ≅ T`. -/
theorem rid_comp_baseChange_rid (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] :
    (TensorProduct.AlgebraTensorModule.rid S T T).toLinearMap ∘ₗ
      LinearMap.baseChange T (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T R).symm.toLinearMap =
      (TensorProduct.AlgebraTensorModule.rid R T T).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul t r =>
    simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearMap.baseChange_tmul, Algebra.smul_def, IsScalarTower.algebraMap_apply R S T]
  | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
/-- The comparison `S ⊗_R R ≅ S` underlying the regular section on a ring map. -/
noncomputable def regularComparison {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (ModuleCat.extendScalars f.hom).obj (ModuleCat.of R R) ⟶ ModuleCat.of S S :=
  letI := f.hom.toAlgebra
  (show ModuleCat.of S (TensorProduct R S R) ⟶ ModuleCat.of S S from
    ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap)

set_option backward.isDefEq.respectTransparency false in
/-- The regular section `R ↦ (R, R)` of the module fibration `∫ Mod → CommRing`: every ring as a
module over itself, transported by `S ⊗_R R ≅ S`. Integral forms are the pullback of `Bil` along
it. -/
noncomputable def regularSection : CommRingCat.{u} ⥤ ModulesOverRingsExt.{u} where
  obj R := ⟨R, ModuleCat.of R R⟩
  map f := ⟨f, regularComparison f⟩
  map_id R := by
    refine Pseudofunctor.Grothendieck.Hom.ext _ _ rfl ?_
    simp
    erw [extendScalarsId_hom_app_eq]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a b
    exact mul_comm _ _
  map_comp {R S T} f g := by
    refine Pseudofunctor.Grothendieck.Hom.ext _ _ rfl ?_
    simp only [eqToHom_refl, Category.id_comp, Pseudofunctor.Grothendieck.categoryStruct_comp_fiber,
      CommRingCat.moduleCatExtendScalarsPseudofunctor_mapComp]
    erw [extendScalarsComp_hom_app_eq f g]
    let _ := f.hom.toAlgebra
    let _ := g.hom.toAlgebra
    let _ := (f ≫ g).hom.toAlgebra
    have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact ModuleCat.hom_ext (rid_comp_baseChange_rid R S T).symm

/-- The projection `p` of forms to their value modules over their rings. -/
abbrev BilinFormsOverRings.values : BilinFormsOverRings.{u} ⥤ ModulesOverRingsExt.{u} :=
  Pseudofunctor.Grothendieck.map valueProjectionTrans

/-- The tower commutes on the nose: `p ⋙ q` is the projection of forms to rings. -/
theorem BilinFormsOverRings.values_comp_ring :
    BilinFormsOverRings.values.{u} ⋙ ModulesOverRingsExt.ring = BilinFormsOverRings.ring :=
  rfl

instance (R : LocallyDiscrete CommRingCat.{u}) :
    (valueProjectionTrans.app R).toFunctor.IsCofibered :=
  inferInstanceAs (CategoryTheory.Grothendieck.forget (valueFibers R.as)).IsCofibered

set_option backward.isDefEq.respectTransparency false in
/-- Base change of the canonical change-of-value lift is value-cocartesian: its carrier map is the
base change of the identity. -/
theorem isStronglyCocartesian_baseChangeAlong_valueBaseChangeHom {R S : CommRingCat.{u}}
    (h : R ⟶ S) (X : BilWFormCat R) {W : ModuleCat.{u} R} (g : X.value ⟶ W) :
    Functor.IsStronglyCocartesian (valueProjection S) ((ModuleCat.extendScalars h.hom).map g)
      ((baseChangeAlong h).map (valueBaseChangeHom R X g)) := by
  have hbij : Function.Bijective (BilinModuleCat.underlyingMap
      ((baseChangeAlong h).map (valueBaseChangeHom R X g)).fiber) := by
    let _ := h.hom.toAlgebra
    have e : BilinModuleCat.underlyingMap
        ((baseChangeAlong h).map (valueBaseChangeHom R X g)).fiber = LinearMap.id :=
      LinearMap.baseChange_id
    rw [e]
    exact Function.bijective_id
  have := BilinModuleCat.isIso_of_bijective _ hbij
  exact CategoryTheory.Grothendieck.isStronglyCocartesian_of_isIso_fiber
    ((baseChangeAlong h).map (valueBaseChangeHom R X g))

/-- Base change preserves value-cocartesian morphisms (FOUNDATIONS 31.2b, hypothesis (2)). -/
theorem baseChangeAlong_isStronglyCocartesian {R S : CommRingCat.{u}} (h : R ⟶ S)
    {X Y : BilWFormCat R} (ψ : X ⟶ Y)
    (hψ : Functor.IsStronglyCocartesian (valueProjection R) ((valueProjection R).map ψ) ψ) :
    Functor.IsStronglyCocartesian (valueProjection S)
      ((valueProjection S).map ((baseChangeAlong h).map ψ)) ((baseChangeAlong h).map ψ) :=
  have := hψ
  Functor.IsStronglyCocartesian.map_of_exists (valueProjection R) (valueProjection S)
    (baseChangeAlong h) (ModuleCat.extendScalars h.hom)
    (baseChangeAlong_comp_valueProjection h)
    (fun X _ g ↦ ⟨_, valueBaseChangeHom R X g, valueBaseChangeHom_isStronglyCocartesian R X g,
      isStronglyCocartesian_baseChangeAlong_valueBaseChangeHom h X g⟩)
    ((valueProjection R).map ψ) ψ

/-- `p : Bil ⥤ ∫Mod` is a cocartesian fibration (FOUNDATIONS Example 31.2c). -/
instance BilinFormsOverRings.isCofibered_values : BilinFormsOverRings.values.{u}.IsCofibered :=
  Pseudofunctor.Grothendieck.isCofibered_map valueProjectionTrans
    fun h _ _ ψ hψ ↦ baseChangeAlong_isStronglyCocartesian h ψ hψ

/-- The fibre of `p : Bil ⥤ ∫ Mod` over `(R, W)` is the category of `W`-valued bilinear forms
over `R` (FOUNDATIONS Proposition 31.2b, fibres; `BilinModuleCat R W` is the fibre of the
change-of-values construction over `W`). -/
noncomputable def BilinFormsOverRings.fibreEquivalence (R : CommRingCat.{u})
    (W : ModuleCat.{u} R) :
    BilinModuleCat R W ≌
      Functor.Fiber BilinFormsOverRings.values (⟨R, W⟩ : ModulesOverRingsExt.{u}) :=
  (CategoryTheory.Grothendieck.fibreEquivalence (valueFibers R) W).trans
    (Pseudofunctor.Grothendieck.fibreEquivalence valueProjectionTrans R W)

end LeanCategories.Lattices.Valued

end

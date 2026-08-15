/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Presentation.Basic

@[expose] public section

namespace LeanCategories.Modules

open CategoryTheory

universe u v w₀ w₁

variable (R : Type u) [Ring R]

/-- A module equipped with a chosen generators-and-relations presentation. -/
structure PresentedModule where
  carrier : ModuleCat.{v} R
  presentation : Module.Presentation.{w₀, w₁} R carrier

namespace PresentedModule

variable {R}

/-- The carrier module of a presented-module object. -/
abbrev carrierObj (X : PresentedModule R) : ModuleCat.{v} R := X.carrier

instance : Category.{v} (PresentedModule R) where
  Hom X Y := X.carrierObj ⟶ Y.carrierObj
  id X := 𝟙 X.carrierObj
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

/-- Forget the chosen presentation and retain the carrier module. -/
def forget : PresentedModule R ⥤ ModuleCat.{v} R where
  obj X := X.carrierObj
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (forget (R := R)).Faithful where
  map_injective h := h

instance : (forget (R := R)).Full where
  map_surjective f := ⟨f, rfl⟩

end PresentedModule

/-!
### Presentation comparison

Fixing the generators and relations gives a category in which a morphism is
the target solution of those relations.  Mathlib's universal property then
turns that solution into the unique map between the presented modules.
-/

universe u'

variable {R : Type u'} [Ring R]

/-- Presented modules over one fixed system of generators and relations. -/
structure PresentedModuleOver
    (relations : Module.Relations.{u', u'} R) where
  carrier : ModuleCat.{u'} R
  solution : relations.Solution (carrier : Type u')
  isPresentation : solution.IsPresentation

namespace PresentedModuleOver

variable {relations : Module.Relations.{u', u'} R}

noncomputable instance : Category (PresentedModuleOver relations) where
  Hom X Y := relations.Solution (Y.carrier : Type u')
  id X := X.solution
  comp {X Y Z} f g := f.postcomp (Y.isPresentation.desc g)
  id_comp {X Y} f := X.isPresentation.postcomp_desc f
  comp_id {X Y} f := by
    have h : Y.isPresentation.desc Y.solution = LinearMap.id := by
      apply Y.isPresentation.postcomp_injective
      simp
    rw [h]
    rfl
  assoc {W X Y Z} f g h := by
    have h' : X.isPresentation.desc (g.postcomp (Y.isPresentation.desc h)) =
        (Y.isPresentation.desc h).comp (X.isPresentation.desc g) := by
      apply X.isPresentation.postcomp_injective
      simp
    rw [h', Module.Relations.Solution.postcomp_comp]

/-- Compare fixed-relations presentations with `PresentedModule`.

The map on morphisms is Mathlib's canonical map induced by the target
solution, rather than an arbitrary map between the underlying carriers.
-/
noncomputable def comparison :
    PresentedModuleOver relations ⥤ PresentedModule.{u', u', u', u'} R where
  obj X :=
    { carrier := X.carrier
      presentation := Module.Presentation.ofIsPresentation X.isPresentation }
  map {X Y} f :=
    ModuleCat.ofHom
      (X.isPresentation.desc (show relations.Solution (Y.carrier : Type u') from f))
  map_id X := by
    apply ModuleCat.hom_ext
    change X.isPresentation.desc X.solution = LinearMap.id
    apply X.isPresentation.postcomp_injective
    simp
  map_comp {X Y Z} f g := by
    change relations.Solution (Y.carrier : Type u') at f
    change relations.Solution (Z.carrier : Type u') at g
    apply ModuleCat.hom_ext
    change X.isPresentation.desc (f.postcomp (Y.isPresentation.desc g)) =
      (Y.isPresentation.desc g).comp (X.isPresentation.desc f)
    apply X.isPresentation.postcomp_injective
    simp

end PresentedModuleOver

end LeanCategories.Modules

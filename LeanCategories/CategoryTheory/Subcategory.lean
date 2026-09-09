/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful

@[expose] public section

open _root_.CategoryTheory

namespace LeanCategories.CategoryTheory

universe v u

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C]

/-- A subcategory specified by selected objects and selected ambient morphisms, closed under
identities and composition (FC03-C01-U014).

Unlike `CategoryTheory.ObjectProperty.FullSubcategory`, this need not be full; unlike
`CategoryTheory.WideSubcategory`, it need not contain every object. -/
structure Subcategory where
  /-- Objects retained in the subcategory. -/
  obj : C → Prop
  /-- Ambient morphisms retained between selected objects. -/
  hom : ∀ {X Y : C}, (X ⟶ Y) → Prop
  /-- The identity of every selected object is retained. -/
  id_mem : ∀ (X : C), obj X → hom (𝟙 X)
  /-- Retained composable morphisms between selected objects are closed under composition. -/
  comp_mem : ∀ {X Y Z : C} (_hX : obj X) (_hY : obj Y) (_hZ : obj Z)
    (f : X ⟶ Y) (g : Y ⟶ Z), hom f → hom g → hom (f ≫ g)

/-- The maximal subgroupoid viewed as a selected subcategory: all objects, only isomorphisms.
This is a positive non-full example of FC03-C01-U014. -/
def coreSubcategory (C : Type u) [_root_.CategoryTheory.Category.{v} C] : Subcategory C where
  obj := fun _ => True
  hom := fun f => _root_.CategoryTheory.IsIso f
  id_mem := by
    intro X hX
    infer_instance
  comp_mem := by
    intro X Y Z hX hY hZ f g hf hg
    exact _root_.CategoryTheory.IsIso.comp_isIso' hf hg

/-- A nonisomorphism is excluded from `coreSubcategory`; this separates general subcategories from
full subcategories on the same object collection. -/
theorem coreSubcategory_excludes_nonIso {C : Type u} [_root_.CategoryTheory.Category.{v} C]
    {X Y : C} (f : X ⟶ Y) (h : ¬ _root_.CategoryTheory.IsIso f) :
    ¬ (coreSubcategory C).hom f := h

namespace Subcategory

variable {C}

/-- Objects of a selected subcategory. -/
def Obj (S : Subcategory C) := {X : C // S.obj X}


/-- Morphisms in the selected subcategory are ambient morphisms satisfying the selected-morphism
predicate. -/
structure Hom (S : Subcategory C) (X Y : S.Obj) where
  /-- The underlying ambient morphism. -/
  hom : (X.1 : C) ⟶ Y.1
  /-- Proof that the morphism is retained. -/
  property : S.hom hom

@[ext]
theorem hom_ext (S : Subcategory C) {X Y : S.Obj} {f g : S.Hom X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance category (S : Subcategory C) : _root_.CategoryTheory.Category.{v} S.Obj where
  Hom X Y := S.Hom X Y
  id X := ⟨𝟙 X.1, S.id_mem X.1 X.2⟩
  comp {X Y Z} f g :=
    ⟨f.hom ≫ g.hom, S.comp_mem X.2 Y.2 Z.2 f.hom g.hom f.property g.property⟩
  id_comp f := by apply hom_ext S; simp
  comp_id f := by apply hom_ext S; simp
  assoc f g h := by apply hom_ext S; simp

/-- The faithful inclusion of a selected subcategory into its ambient category. -/
def inclusion (S : Subcategory C) : S.Obj ⥤ C where
  obj X := X.1
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

instance inclusionFaithful (S : Subcategory C) : _root_.CategoryTheory.Functor.Faithful S.inclusion where
  map_injective h := hom_ext S h

end Subcategory

end LeanCategories.CategoryTheory

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

open CategoryTheory

namespace LeanCategories.Modules

universe u

variable (R : Type u) [CommRing R]
variable (n : ℕ)

/-- The standard free `R`-module of rank `n`. -/
abbrev StandardFreeModule := ModuleCat.of R (Fin n → R)

/-- A rank-`n` frame is a map from the standard free module. -/
abbrev FrameArrow :=
  StructuredArrow (StandardFreeModule R n) (𝟭 (ModuleCat.{u} R))

/-- Generating frames are the surjective frame arrows. -/
def isGenFrame : ObjectProperty (FrameArrow R n) :=
  (MorphismProperty.epimorphisms (ModuleCat.{u} R)).structuredArrowObj
    (𝟭 (ModuleCat.{u} R))

/-- Modules with a selected rank-`n` generating frame. -/
abbrev GenFrame := (isGenFrame R n).FullSubcategory

/-- Basis frames are the invertible frame arrows. -/
def isBasisFrame : ObjectProperty (FrameArrow R n) :=
  (MorphismProperty.isomorphisms (ModuleCat.{u} R)).structuredArrowObj
    (𝟭 (ModuleCat.{u} R))

/-- Modules with a selected rank-`n` basis frame and frame-preserving morphisms. -/
abbrev BasisFrame := (isBasisFrame R n).FullSubcategory

/-- Forget that an invertible frame is generating. -/
def basisFrameToGenFrame : BasisFrame R n ⥤ GenFrame R n :=
  ObjectProperty.ιOfLE fun X hX ↦ by
    letI : IsIso X.hom := by
      change IsIso X.hom at hX
      exact hX
    exact MorphismProperty.epimorphisms.infer_property X.hom

/-- A coordinatized module has a selected basis frame.

Morphisms are arbitrary linear maps. They do not preserve the selected frames. -/
@[ext]
structure Coord where
  frame : BasisFrame R n

namespace Coord

/-- The module presented by a coordinatized object. -/
abbrev carrierObj (X : Coord R n) : ModuleCat.{u} R := X.frame.obj.right

instance : Category.{u} (Coord R n) where
  Hom X Y := X.carrierObj ⟶ Y.carrierObj
  id X := 𝟙 X.carrierObj
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

/-- Forget coordinates and retain the underlying module. -/
def forget : Coord R n ⥤ ModuleCat.{u} R where
  obj X := X.carrierObj
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (forget R n).Faithful where
  map_injective h := h

instance : (forget R n).Full where
  map_surjective f := ⟨f, rfl⟩

/-- Regard a basis-frame object as a coordinatized object. -/
def fromBasisFrame : BasisFrame R n ⥤ Coord R n where
  obj X := ⟨X⟩
  map f := f.hom.right
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (fromBasisFrame R n).Faithful where
  map_injective h := by
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    exact h

/-- Construct coordinates from an isomorphism with the standard free module. -/
def ofIso {M : ModuleCat R} (e : StandardFreeModule R n ≅ M) : Coord R n :=
  ⟨⟨StructuredArrow.mk e.hom, by
    change IsIso e.hom
    infer_instance⟩⟩

/-- The selected basis frame as an isomorphism of modules. -/
noncomputable def frameIso (X : Coord R n) :
    StandardFreeModule R n ≅ X.carrierObj := by
  exact @asIso (ModuleCat R) _ _ _ X.frame.obj.hom (by
    change IsIso X.frame.obj.hom
    exact X.frame.property)

end Coord

end LeanCategories.Modules

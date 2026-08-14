/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import LeanCategories.Modules.Mathlib

@[expose] public section

noncomputable section

open CategoryTheory

namespace LeanCategories.Modules

universe u v

variable (R : Type u) [CommRing R]
variable (I : Type v)

/-- The standard free `R`-module on the indexing type `I`. -/
abbrev StandardFreeModule := ModuleCat.of R (I →₀ R)

/-- A frame is a map from the standard free module. -/
abbrev FrameArrow :=
  StructuredArrow (StandardFreeModule R I) (𝟭 (ModuleCat.{max u v} R))

/-- Generating frames are the surjective frame arrows. -/
def isGenFrame : ObjectProperty (FrameArrow R I) :=
  (MorphismProperty.epimorphisms (ModuleCat.{max u v} R)).structuredArrowObj
    (𝟭 (ModuleCat.{max u v} R))

/-- Modules with a selected generating frame. -/
abbrev GenFrame := (isGenFrame R I).FullSubcategory

/-- Modules carrying a specified generating frame. -/
abbrev FramedModules := GenFrame

namespace GenFrame

/-- Forget a generating frame and retain its carrier module. -/
def forget : GenFrame R I ⥤ ModuleCat.{max u v} R where
  obj X := X.obj.right
  map f := f.hom.right
  map_id _ := rfl
  map_comp _ _ := rfl

end GenFrame

namespace FramedModules

/-- Forget the specified generating frame and retain the carrier module. -/
def forget : FramedModules R I ⥤ ModuleCat.{max u v} R :=
  GenFrame.forget R I

end FramedModules

/-- Free modules carrying a specified generating frame. -/
def isFramedFreeModule : ObjectProperty (GenFrame R I) :=
  fun X => Module.Free R X.obj.right

/-- The full subcategory of free modules with a selected generating frame. -/
abbrev FramedFreeModules := (isFramedFreeModule R I).FullSubcategory

namespace FramedFreeModules

/-- Forget the selected generating frame and retain the carrier module. -/
def forget : FramedFreeModules R I ⥤ ModuleCat.{max u v} R :=
  ObjectProperty.ι (isFramedFreeModule R I) ⋙ GenFrame.forget R I

/-- Retain the free-module property after forgetting the selected frame. -/
def toFreeModuleCat : FramedFreeModules R I ⥤
    LeanCategories.Modules.Mathlib.FreeModuleCat (RingCat.of R) where
  obj X := ⟨(forget R I).obj X, X.property⟩
  map f := ObjectProperty.homMk ((forget R I).map f)
  map_id _ := rfl
  map_comp _ _ := rfl

end FramedFreeModules

/-- Basis frames are the invertible frame arrows. -/
def isBasisFrame : ObjectProperty (FrameArrow R I) :=
  (MorphismProperty.isomorphisms (ModuleCat.{max u v} R)).structuredArrowObj
    (𝟭 (ModuleCat.{max u v} R))

/-- Modules with a selected basis frame and frame-preserving morphisms. -/
abbrev BasisFrame := (isBasisFrame R I).FullSubcategory

namespace BasisFrame

/-- Forget a basis frame and retain its carrier module. -/
def forget : BasisFrame R I ⥤ ModuleCat.{max u v} R where
  obj X := X.obj.right
  map f := f.hom.right
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Expose a basis frame as a free module while retaining its carrier basis property. -/
def toFreeModuleCat : BasisFrame R I ⥤
    LeanCategories.Modules.Mathlib.FreeModuleCat (RingCat.of R) where
  obj X := by
    letI : IsIso X.obj.hom := X.property
    let e : StandardFreeModule R I ≅ X.obj.right :=
      @asIso (ModuleCat R) _ _ _ X.obj.hom (by
        change IsIso X.obj.hom
        exact X.property)
    exact ⟨X.obj.right,
      Module.Free.of_basis (Module.Basis.ofRepr e.toLinearEquiv.symm)⟩
  map f := ObjectProperty.homMk ((forget R I).map f)
  map_id _ := rfl
  map_comp _ _ := rfl

end BasisFrame

/-- Forget that an invertible frame is generating. -/
def basisFrameToGenFrame : BasisFrame R I ⥤ GenFrame R I :=
  ObjectProperty.ιOfLE fun X hX ↦ by
    letI : IsIso X.hom := by
      change IsIso X.hom at hX
      exact hX
    exact MorphismProperty.epimorphisms.infer_property X.hom

namespace FrameArrow

/-- Change the source of a frame along an isomorphism of standard free modules. -/
noncomputable def sourceIso {I J : Type v}
    (e : StandardFreeModule R I ≅ StandardFreeModule R J) :
    FrameArrow R I ≌ FrameArrow R J :=
  StructuredArrow.mapIso e

/-- Reindex a frame along an equivalence of its indexing types. -/
noncomputable def reindex {I J : Type v} (e : I ≃ J) :
    FrameArrow R I ≌ FrameArrow R J :=
  sourceIso R (Finsupp.mapDomain.linearEquiv R R e).toModuleIso

end FrameArrow

/-- A coordinatized module has a selected basis frame.

Morphisms are arbitrary linear maps. They do not preserve the selected frames. -/
@[ext]
structure Coord where
  frame : BasisFrame R I

namespace Coord

/-- The module presented by a coordinatized object. -/
abbrev carrierObj (X : Coord R I) : ModuleCat.{max u v} R := X.frame.obj.right

instance : Category.{max u v} (Coord R I) where
  Hom X Y := X.carrierObj ⟶ Y.carrierObj
  id X := 𝟙 X.carrierObj
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

/-- Forget coordinates and retain the underlying module. -/
def forget : Coord R I ⥤ ModuleCat.{max u v} R where
  obj X := X.carrierObj
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (forget R I).Faithful where
  map_injective h := h

instance : (forget R I).Full where
  map_surjective f := ⟨f, rfl⟩

/-- Regard a basis-frame object as a coordinatized object. -/
def fromBasisFrame : BasisFrame R I ⥤ Coord R I where
  obj X := ⟨X⟩
  map f := f.hom.right
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (fromBasisFrame R I).Faithful where
  map_injective h := by
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    exact h

/-- Construct coordinates from an isomorphism with the standard free module. -/
def ofIso {M : ModuleCat.{max u v} R} (e : StandardFreeModule R I ≅ M) : Coord R I :=
  ⟨⟨StructuredArrow.mk e.hom, by
    change IsIso e.hom
    infer_instance⟩⟩

/-- The selected basis frame as an isomorphism of modules. -/
noncomputable def frameIso (X : Coord R I) :
    StandardFreeModule R I ≅ X.carrierObj := by
  exact @asIso (ModuleCat R) _ _ _ X.frame.obj.hom (by
    change IsIso X.frame.obj.hom
    exact X.frame.property)

/-! A coordinatized module is free because its selected frame is a basis. -/

def toFreeModuleCat : Coord R I ⥤
    LeanCategories.Modules.Mathlib.FreeModuleCat (RingCat.of R) where
  obj X := ⟨X.carrierObj,
    Module.Free.of_basis (Module.Basis.ofRepr (frameIso R I X).toLinearEquiv.symm)⟩
  map f := ObjectProperty.homMk ((forget R I).map f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-! A coordinatized module of finite index has finite rank. -/

def toFiniteRankModuleCat [Finite I] : Coord R I ⥤
    LeanCategories.Modules.Mathlib.FiniteRankModuleCat (RingCat.of R) where
  obj X := by
    let b : Module.Basis I R X.carrierObj :=
      Module.Basis.ofRepr (frameIso R I X).toLinearEquiv.symm
    letI : Module.Free R X.carrierObj := Module.Free.of_basis b
    letI : Module.Finite R X.carrierObj := Module.Finite.of_basis b
    exact ⟨X.carrierObj, ⟨inferInstance,
      Finite.of_fintype (Module.Free.ChooseBasisIndex R X.carrierObj)⟩⟩
  map f := ObjectProperty.homMk ((forget R I).map f)
  map_id _ := rfl
  map_comp _ _ := rfl

end Coord

end LeanCategories.Modules

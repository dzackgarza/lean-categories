/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import LeanCategories.Modules.Mathlib

@[expose] public section

/-!
# Truncated free resolutions: free covers and bases

FOUNDATIONS Defs. 13.10–13.11: an augmented free resolution `⋯ → F₁ → F₀ → M → 0` truncates to
a *free cover* `R^(I) ↠ M` (1-truncated: a chosen surjection from a free module, i.e. chosen
generators) and, when the augmentation is invertible, to a free resolution of length zero
`R^(I) ≅ M` (a chosen basis). These replace the former "generating frames" and "basis frames"
(FOUNDATIONS Defs. 13.5–13.6, superseded): "frame" is reserved for framings of bundles
(Remark 13.12). Maps of truncated resolutions are the maps of augmented complexes; `Coord` keeps a
chosen basis but admits all linear maps.
-/

noncomputable section

open CategoryTheory

namespace LeanCategories.Modules

universe u v

variable (R : Type u) [CommRing R]
variable (I : Type v)

/-- Two matrices present isomorphic maps between finite free modules when they lie in the
same left-right orbit of the target and source general linear groups. -/
def Matrix.Equivalent {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {R : Type*} [Semiring R] (A B : Matrix m n R) : Prop :=
  ∃ P : Matrix.GeneralLinearGroup m R, ∃ Q : Matrix.GeneralLinearGroup n R,
    B = (P : Matrix m m R) * A * (Q : Matrix n n R)

/-- The standard free `R`-module on the indexing type `I`. -/
abbrev StandardFreeModule := ModuleCat.of R (I →₀ R)

/-- The degree-zero part of an augmented free resolution indexed by `I`: a map
`ε : R^(I) → M` from the standard free module (FOUNDATIONS Def. 13.10). -/
abbrev FreeAugmentation :=
  StructuredArrow (StandardFreeModule R I) (𝟭 (ModuleCat.{max u v} R))

/-- A 1-truncated free resolution `R^(I) ↠ M → 0`: a surjective augmentation (FOUNDATIONS
Def. 13.11). -/
def isFreeCover : ObjectProperty (FreeAugmentation R I) :=
  (MorphismProperty.epimorphisms (ModuleCat.{max u v} R)).structuredArrowObj
    (𝟭 (ModuleCat.{max u v} R))

/-- Modules with a chosen free cover `R^(I) ↠ M`: 1-truncated free resolutions, with maps of
augmented complexes. -/
abbrev FreeCover := (isFreeCover R I).FullSubcategory

namespace FreeCover

/-- Forget the free cover and retain the module. -/
def forget : FreeCover R I ⥤ ModuleCat.{max u v} R where
  obj X := X.obj.right
  map f := f.hom.right
  map_id _ := rfl
  map_comp _ _ := rfl

end FreeCover

/-- Free modules with a chosen free cover. -/
def isFreeCoveredFreeModule : ObjectProperty (FreeCover R I) :=
  fun X => Module.Free R X.obj.right

/-- The full subcategory of free modules with a chosen free cover. -/
abbrev FreeCoveredFreeModules := (isFreeCoveredFreeModule R I).FullSubcategory

namespace FreeCoveredFreeModules

/-- Forget the chosen free cover and retain the module. -/
def forget : FreeCoveredFreeModules R I ⥤ ModuleCat.{max u v} R :=
  ObjectProperty.ι (isFreeCoveredFreeModule R I) ⋙ FreeCover.forget R I

/-- Retain the free-module property after forgetting the chosen cover. -/
def toFreeModuleCat : FreeCoveredFreeModules R I ⥤
    LeanCategories.Modules.Mathlib.FreeModuleCat (RingCat.of R) where
  obj X := ⟨(forget R I).obj X, X.property⟩
  map f := ObjectProperty.homMk ((forget R I).map f)
  map_id _ := rfl
  map_comp _ _ := rfl

end FreeCoveredFreeModules

/-- A free resolution of length zero `R^(I) ≅ M`: an invertible augmentation, i.e. a chosen
basis (FOUNDATIONS Def. 13.11). -/
def isBasedModule : ObjectProperty (FreeAugmentation R I) :=
  (MorphismProperty.isomorphisms (ModuleCat.{max u v} R)).structuredArrowObj
    (𝟭 (ModuleCat.{max u v} R))

/-- Modules with a chosen basis (length-zero free resolutions), with basis-preserving maps. -/
abbrev BasedModule := (isBasedModule R I).FullSubcategory

namespace BasedModule

/-- Forget the chosen basis and retain the module. -/
def forget : BasedModule R I ⥤ ModuleCat.{max u v} R where
  obj X := X.obj.right
  map f := f.hom.right
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A based module is free. -/
def toFreeModuleCat : BasedModule R I ⥤
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

end BasedModule

/-- A length-zero free resolution is in particular 1-truncated: an isomorphism is surjective. -/
def basedModuleToFreeCover : BasedModule R I ⥤ FreeCover R I :=
  ObjectProperty.ιOfLE fun X hX ↦ by
    letI : IsIso X.hom := by
      change IsIso X.hom at hX
      exact hX
    exact MorphismProperty.epimorphisms.infer_property X.hom

namespace FreeAugmentation

/-- Change the source of an augmentation along an isomorphism of standard free modules. -/
noncomputable def sourceIso {I J : Type v}
    (e : StandardFreeModule R I ≅ StandardFreeModule R J) :
    FreeAugmentation R I ≌ FreeAugmentation R J :=
  StructuredArrow.mapIso e

/-- Reindex an augmentation along an equivalence of its indexing types. -/
noncomputable def reindex {I J : Type v} (e : I ≃ J) :
    FreeAugmentation R I ≌ FreeAugmentation R J :=
  sourceIso R (Finsupp.mapDomain.linearEquiv R R e).toModuleIso

end FreeAugmentation

/-- A coordinatized module: a module with a chosen basis.

Morphisms are arbitrary linear maps. They do not preserve the chosen bases. -/
@[ext]
structure Coord where
  basis : BasedModule R I

namespace Coord

/-- The module presented by a coordinatized object. -/
abbrev carrierObj (X : Coord R I) : ModuleCat.{max u v} R := X.basis.obj.right

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

/-- Regard a based module as a coordinatized module. -/
def fromBasedModule : BasedModule R I ⥤ Coord R I where
  obj X := ⟨X⟩
  map f := f.hom.right
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (fromBasedModule R I).Faithful where
  map_injective h := by
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    exact h

/-- Construct coordinates from an isomorphism with the standard free module. -/
def ofIso {M : ModuleCat.{max u v} R} (e : StandardFreeModule R I ≅ M) : Coord R I :=
  ⟨⟨StructuredArrow.mk e.hom, by
    change IsIso e.hom
    infer_instance⟩⟩

/-- The chosen basis as an isomorphism of modules. -/
noncomputable def basisIso (X : Coord R I) :
    StandardFreeModule R I ≅ X.carrierObj := by
  exact @asIso (ModuleCat R) _ _ _ X.basis.obj.hom (by
    change IsIso X.basis.obj.hom
    exact X.basis.property)

/-! A coordinatized module is free because it has a basis. -/

def toFreeModuleCat : Coord R I ⥤
    LeanCategories.Modules.Mathlib.FreeModuleCat (RingCat.of R) where
  obj X := ⟨X.carrierObj,
    Module.Free.of_basis (Module.Basis.ofRepr (basisIso R I X).toLinearEquiv.symm)⟩
  map f := ObjectProperty.homMk ((forget R I).map f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-! A coordinatized module of finite index has finite rank. -/

def toFiniteRankModuleCat [Finite I] : Coord R I ⥤
    LeanCategories.Modules.Mathlib.FiniteRankModuleCat (RingCat.of R) where
  obj X := by
    let b : Module.Basis I R X.carrierObj :=
      Module.Basis.ofRepr (basisIso R I X).toLinearEquiv.symm
    letI : Module.Free R X.carrierObj := Module.Free.of_basis b
    letI : Module.Finite R X.carrierObj := Module.Finite.of_basis b
    exact ⟨X.carrierObj, ⟨inferInstance,
      Finite.of_fintype (Module.Free.ChooseBasisIndex R X.carrierObj)⟩⟩
  map f := ObjectProperty.homMk ((forget R I).map f)
  map_id _ := rfl
  map_comp _ _ := rfl

end Coord

end LeanCategories.Modules

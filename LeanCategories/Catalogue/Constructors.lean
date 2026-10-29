/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryTheory.OneCat.Universes
public import Mathlib.CategoryTheory.Comma.Arrow
public import LeanCategories.CategoryTheory.OneCat.KernelFunctor
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Category

@[expose] public section

/-!
# Semantics of the typed category constructors (#54 §1, CC-CALC)

Each registered constructor denotes one of these Lean definitions, and each is an existing
Mathlib construction: the arrow category (`Arrow`), the core (`Core`), slices and coslices
(`Over`, `Under`), categories of elements (`Functor.Elements`), functor categories, and the
category of subobjects of `C`, the full subcategory of `Arrow C` on monomorphisms with commutative
squares as morphisms (#54 §1). Registration checks that a category built by a constructor is
definitionally its semantics applied to the registered denotations of its arguments.

The comparison interfaces reuse Mathlib's `Functor.mapArrowFunctor.mapIso` and `Iso.core`,
including `Functor.mapIso_refl`, `Functor.mapIso_trans`, `Iso.coreId`, and `Iso.coreComp`.
The core identity and composition comparisons are `Functor.coreId` and `Functor.coreComp`;
the arrow comparisons have definitionally equal endpoints in `Comma/Arrow.lean`.
-/

namespace CasCatalogue.Constructors
open LeanCategories

open CategoryTheory

universe u v w x y z

/-- `Arr(C)`: the arrow category. -/
def arrow (C : ObjCat.{u, v}) : ObjCat.{max u v, v} := Cat.of (Arrow C)

/-- `Arr(F)`: a functor acts on arrows (Mathlib `Functor.mapArrow`). -/
def arrowMap {C : ObjCat.{u, v}} {D : ObjCat.{w, x}} (F : C ⥤ D) : arrow C ⥤ arrow D :=
  F.mapArrow

/-- The arrow constructor sends a natural isomorphism to the isomorphism of arrow functors
supplied by Mathlib's functor on the functor category. -/
def arrowComparison {C : ObjCat.{u, v}} {D : ObjCat.{w, x}} {F G : C ⥤ D}
    (α : F ≅ G) : arrowMap F ≅ arrowMap G :=
  (Functor.mapArrowFunctor C D).mapIso α

/-- The arrow action preserves the identity functor. -/
def arrowIdentityComparison (C : ObjCat.{u, v}) : arrowMap (𝟭 C) ≅ 𝟭 (arrow C) :=
  Iso.refl _

/-- The arrow action preserves composition of functors. -/
def arrowCompositionComparison {C : ObjCat.{u, v}} {D : ObjCat.{w, x}}
    {E : ObjCat.{y, z}} (F : C ⥤ D) (G : D ⥤ E) :
    arrowMap (F ⋙ G) ≅ arrowMap F ⋙ arrowMap G :=
  Iso.refl _

@[simp]
theorem arrowComparison_refl {C : ObjCat.{u, v}} {D : ObjCat.{w, x}} (F : C ⥤ D) :
    arrowComparison (Iso.refl F) = Iso.refl (arrowMap F) := by
  exact Functor.mapIso_refl _ _

@[simp]
theorem arrowComparison_trans {C : ObjCat.{u, v}} {D : ObjCat.{w, x}}
    {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) :
    arrowComparison (α ≪≫ β) = arrowComparison α ≪≫ arrowComparison β := by
  exact Functor.mapIso_trans _ _ _

/-- The left component retains the supplied natural isomorphism, including nonidentity maps. -/
@[simp]
theorem arrowComparison_hom_left {C : ObjCat.{u, v}} {D : ObjCat.{w, x}}
    {F G : C ⥤ D} (α : F ≅ G) (f : Arrow C) :
    ((arrowComparison α).hom.app f).left = α.hom.app f.left := rfl

/-- The right component retains the supplied natural isomorphism. -/
@[simp]
theorem arrowComparison_hom_right {C : ObjCat.{u, v}} {D : ObjCat.{w, x}}
    {F G : C ⥤ D} (α : F ≅ G) (f : Arrow C) :
    ((arrowComparison α).hom.app f).right = α.hom.app f.right := rfl

/-- `Core(C)`: the maximal subgroupoid. -/
def core (C : ObjCat.{u, v}) : ObjCat.{max u v, v} := Cat.of (Core C)

/-- `Core(F)`: a functor acts on cores (Mathlib `Functor.core`). -/
def coreMap {C : ObjCat.{u, v}} {D : ObjCat.{w, x}} (F : C ⥤ D) : core C ⥤ core D :=
  F.core

/-- A natural isomorphism acts on the maximal subgroupoids by Mathlib's `Iso.core`. -/
def coreComparison {C : ObjCat.{u, v}} {D : ObjCat.{w, x}} {F G : C ⥤ D}
    (α : F ≅ G) : coreMap F ≅ coreMap G :=
  α.core

/-- The core action's identity comparison. -/
def coreIdentityComparison (C : ObjCat.{u, v}) : coreMap (𝟭 C) ≅ 𝟭 (core C) :=
  Functor.coreId C

/-- The core action's composition comparison. -/
def coreCompositionComparison {C : ObjCat.{u, v}} {D : ObjCat.{w, x}}
    {E : ObjCat.{y, z}} (F : C ⥤ D) (G : D ⥤ E) :
    coreMap (F ⋙ G) ≅ coreMap F ⋙ coreMap G :=
  F.coreComp G

@[simp]
theorem coreComparison_refl {C : ObjCat.{u, v}} {D : ObjCat.{w, x}} (F : C ⥤ D) :
    coreComparison (Iso.refl F) = Iso.refl (coreMap F) :=
  Iso.coreId

@[simp]
theorem coreComparison_trans {C : ObjCat.{u, v}} {D : ObjCat.{w, x}}
    {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) :
    coreComparison (α ≪≫ β) = coreComparison α ≪≫ coreComparison β :=
  Iso.coreComp α β

/-- The core component retains the entire supplied component isomorphism. -/
@[simp]
theorem coreComparison_hom_iso {C : ObjCat.{u, v}} {D : ObjCat.{w, x}}
    {F G : C ⥤ D} (α : F ≅ G) (X : Core C) :
    ((coreComparison α).hom.app X).iso = α.app X.of := rfl

/-- `Slice(C, X)`: the category of objects over `X`. -/
def slice (C : ObjCat.{u, v}) (X : C) : ObjCat.{max u v, v} := Cat.of (Over X)

/-- `Coslice(C, X)`: the category of objects under `X`. -/
def coslice (C : ObjCat.{u, v}) (X : C) : ObjCat.{max u v, v} := Cat.of (Under X)

/-- `Elements(U)`: the category of elements of a set-valued functor. -/
def elements (C : ObjCat.{u, v}) (U : C ⥤ Type v) : ObjCat.{max u v, v} :=
  Cat.of U.Elements

/-- The monomorphism property on arrows (owned by `LeanCategories.isMonoArrow`). -/
abbrev isMonoArrow (C : ObjCat.{u, v}) : ObjectProperty (Arrow C) := LeanCategories.isMonoArrow C

/-- `Subobjects(C)`: the full subcategory of `Arr(C)` on monomorphisms. -/
def subobjects (C : ObjCat.{u, v}) : ObjCat.{max u v, v} :=
  Cat.of (isMonoArrow C).FullSubcategory

/-- `Fun(C, D)`: the functor category. -/
def functorCategory (C : ObjCat.{u, v}) (D : ObjCat.{w, x}) :
    ObjCat.{max u v w x, max u v x} :=
  Cat.of (C ⥤ D)

end CasCatalogue.Constructors

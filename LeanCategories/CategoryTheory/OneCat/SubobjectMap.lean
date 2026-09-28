/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryTheory.OneCat.KernelFunctor
public import Mathlib.CategoryTheory.Functor.EpiMono

@[expose] public section

/-!
# Subobjects along a monomorphism-preserving functor

A functor `F : C ⥤ D` that preserves monomorphisms carries a subobject `A ↪ X` of `C` to the
subobject `F A ↪ F X` of `D`: the functor `Subobjects(C) ⥤ Subobjects(D)` induced by
`F.mapArrow` on the full subcategories of arrows on monomorphisms. For the forgetful functor of
`R`-modules (a right adjoint, hence mono-preserving) it sends a submodule to its underlying subset.
-/

open CategoryTheory

namespace LeanCategories

universe v v' u u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- `Subobjects(C) ⥤ Subobjects(D)`, `(A ↪ X) ↦ (F A ↪ F X)`. -/
def subobjectMap (F : C ⥤ D) [F.PreservesMonomorphisms] :
    (isMonoArrow C).FullSubcategory ⥤ (isMonoArrow D).FullSubcategory :=
  (isMonoArrow D).lift ((isMonoArrow C).ι ⋙ F.mapArrow) fun A =>
    show Mono (F.map A.obj.hom) from
      haveI : Mono A.obj.hom := A.property
      inferInstance

@[simp] theorem subobjectMap_obj_obj (F : C ⥤ D) [F.PreservesMonomorphisms]
    (A : (isMonoArrow C).FullSubcategory) :
    ((subobjectMap F).obj A).obj = F.mapArrow.obj A.obj := rfl

end LeanCategories

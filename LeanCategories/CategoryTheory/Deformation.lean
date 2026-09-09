/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryTheory.Homotopical
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

open _root_.CategoryTheory

namespace LeanCategories.CategoryTheory

universe v u v' u'

variable {C : Type u} [_root_.CategoryTheory.Category.{v} C]
variable [HomotopicalCategory C]

/-- A natural transformation between endofunctors of a homotopical category is a natural weak
 equivalence when every component is a weak equivalence. This is the componentwise condition in
 Riehl Definition 6.4.10. -/
def IsNaturalWeakEquivalence {F G : C ⥤ C} (α : F ⟶ G) : Prop :=
  ∀ X : C, HomotopicalCategory.W C (α.app X)

/-- The identity natural transformation is a natural weak equivalence. -/
theorem isNaturalWeakEquivalence_id (F : C ⥤ C) :
    IsNaturalWeakEquivalence (𝟙 F) := by
  intro X
  change (HomotopicalCategory.weakEquivalences (C := C)).morphisms (𝟙 (F.obj X))
  exact (HomotopicalCategory.weakEquivalences (C := C)).id_mem (F.obj X)

/-- A single non-weak component separates a natural transformation from a natural weak
 equivalence. -/
theorem not_isNaturalWeakEquivalence_of_app_not_weak {F G : C ⥤ C} (α : F ⟶ G)
    (X : C) (h : ¬ HomotopicalCategory.W C (α.app X)) :
    ¬ IsNaturalWeakEquivalence α := by
  intro hα
  exact h (hα X)

/-- A left deformation of a homotopical category is an endofunctor `Q` equipped with a natural
 weak equivalence `q : Q ⟶ 𝟭 C` (FC03-C06-U035). -/
structure LeftDeformation (C : Type u) [_root_.CategoryTheory.Category.{v} C]
    [HomotopicalCategory C] where
  /-- The deformation endofunctor. -/
  Q : C ⥤ C
  /-- The comparison to the identity. -/
  q : Q ⟶ 𝟭 C
  /-- Every comparison component is weak. -/
  q_weak : IsNaturalWeakEquivalence q

/-- A right deformation is the dual datum `r : 𝟭 C ⟶ R` with componentwise weak comparison
 (FC03-C06-U035). -/
structure RightDeformation (C : Type u) [_root_.CategoryTheory.Category.{v} C]
    [HomotopicalCategory C] where
  /-- The deformation endofunctor. -/
  R : C ⥤ C
  /-- The comparison from the identity. -/
  r : 𝟭 C ⟶ R
  /-- Every comparison component is weak. -/
  r_weak : IsNaturalWeakEquivalence r

namespace LeftDeformation

/-- The identity endofunctor with identity comparison is the basic positive left deformation. -/
def identity (C : Type u) [_root_.CategoryTheory.Category.{v} C] [HomotopicalCategory C] :
    LeftDeformation C where
  Q := 𝟭 C
  q := 𝟙 _
  q_weak := isNaturalWeakEquivalence_id _

end LeftDeformation

namespace RightDeformation

/-- The identity endofunctor with identity comparison is the basic positive right deformation. -/
def identity (C : Type u) [_root_.CategoryTheory.Category.{v} C] [HomotopicalCategory C] :
    RightDeformation C where
  R := 𝟭 C
  r := 𝟙 _
  r_weak := isNaturalWeakEquivalence_id _

end RightDeformation

variable {D : Type u'} [_root_.CategoryTheory.Category.{v'} D]
variable [HomotopicalCategory D]

/-- A left deformation for `F : C ⥤ D` is a left deformation of `C` together with a full
 subcategory containing the image of `Q` on which `F` preserves all weak equivalences
 (FC03-C06-U035). The full subcategory is represented by its object property. -/
structure LeftDeformationFor (F : C ⥤ D) where
  /-- The underlying left deformation of the source. -/
  deformation : LeftDeformation C
  /-- Objects of the full subcategory on which `F` is required to preserve weak equivalences. -/
  objects : _root_.CategoryTheory.ObjectProperty C
  /-- The full subcategory contains every object in the image of the deformation functor. -/
  image_mem : ∀ X : C, objects (deformation.Q.obj X)
  /-- `F` preserves weak equivalences between any two selected objects. -/
  map_weak : ∀ {X Y : C}, objects X → objects Y → (f : X ⟶ Y) →
    HomotopicalCategory.W C f → HomotopicalCategory.W D (F.map f)

/-- The dual right-deformation datum for a functor. -/
structure RightDeformationFor (F : C ⥤ D) where
  /-- The underlying right deformation of the source. -/
  deformation : RightDeformation C
  /-- Objects of the full subcategory on which `F` is required to preserve weak equivalences. -/
  objects : _root_.CategoryTheory.ObjectProperty C
  /-- The full subcategory contains every object in the image of the deformation functor. -/
  image_mem : ∀ X : C, objects (deformation.R.obj X)
  /-- `F` preserves weak equivalences between any two selected objects. -/
  map_weak : ∀ {X Y : C}, objects X → objects Y → (f : X ⟶ Y) →
    HomotopicalCategory.W C f → HomotopicalCategory.W D (F.map f)

/-- Every homotopical functor admits the identity left deformation on the full subcategory of all
 objects. This is the positive model for `LeftDeformationFor`. -/
def LeftDeformationFor.ofIsHomotopical (F : C ⥤ D) (hF : IsHomotopical F) :
    LeftDeformationFor F where
  deformation := LeftDeformation.identity C
  objects := ⊤
  image_mem := by intro X; trivial
  map_weak := by
    intro X Y hX hY f hf
    exact hF f hf

/-- Every homotopical functor admits the identity right deformation on the full subcategory of all
 objects. -/
def RightDeformationFor.ofIsHomotopical (F : C ⥤ D) (hF : IsHomotopical F) :
    RightDeformationFor F where
  deformation := RightDeformation.identity C
  objects := ⊤
  image_mem := by intro X; trivial
  map_weak := by
    intro X Y hX hY f hf
    exact hF f hf

end LeanCategories.CategoryTheory

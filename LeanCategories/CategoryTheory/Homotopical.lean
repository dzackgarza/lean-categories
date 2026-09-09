/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic

@[expose] public section

open _root_.CategoryTheory

namespace LeanCategories.CategoryTheory

universe v u v' u'

variable {C : Type u} [_root_.CategoryTheory.Category.{v} C]

/-- The 2-of-6 property for a class of morphisms: for composable `f`, `g`, `h`, membership of
`f ≫ g` and `g ≫ h` forces `f`, `g`, `h`, and `f ≫ g ≫ h` into the class
(FC03-C06-U026). -/
def TwoOfSix (W : _root_.CategoryTheory.MorphismProperty C) : Prop :=
  ∀ {X Y Z T : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
    W (f ≫ g) → W (g ≫ h) → W f ∧ W g ∧ W h ∧ W (f ≫ g ≫ h)

/-- A class of weak equivalences in Riehl's sense: identities are weak equivalences and the class
satisfies 2-of-6 (FC03-C06-U026). -/
structure WeakEquivalences (C : Type u) [_root_.CategoryTheory.Category.{v} C] where
  /-- The underlying class of morphisms. -/
  morphisms : _root_.CategoryTheory.MorphismProperty C
  /-- Every identity is a weak equivalence. -/
  id_mem : ∀ X : C, morphisms (𝟙 X)
  /-- The 2-of-6 axiom. -/
  twoOfSix : TwoOfSix morphisms

/-- The maximal class of all morphisms is a class of weak equivalences. This is a positive model
for the source definition and checks that no unintended closure hypothesis was added. -/
def WeakEquivalences.all (C : Type u) [_root_.CategoryTheory.Category.{v} C] :
    WeakEquivalences C where
  morphisms := ⊤
  id_mem := fun _ => by simp
  twoOfSix := by
    intro X Y Z T f g h hfg hgh
    exact ⟨by simp, by simp, by simp, by simp⟩

/-- Separating criterion for 2-of-6: a composable triple whose two adjacent composites are in `W`
but one of the four required conclusions is absent witnesses failure of the source axiom. -/
theorem not_twoOfSix_of_counterexample (W : _root_.CategoryTheory.MorphismProperty C)
    {X Y Z T : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (hfg : W (f ≫ g)) (hgh : W (g ≫ h))
    (hbad : ¬ (W f ∧ W g ∧ W h ∧ W (f ≫ g ≫ h))) :
    ¬ TwoOfSix W := by
  intro hW
  exact hbad (hW f g h hfg hgh)

/-- A homotopical category is a category equipped with a specified class of weak equivalences
(FC03-C06-U028). -/
class HomotopicalCategory (C : Type u) [_root_.CategoryTheory.Category.{v} C] where
  /-- The chosen weak-equivalence structure. -/
  weakEquivalences : WeakEquivalences C

namespace HomotopicalCategory

/-- The chosen weak-equivalence morphism property. -/
def W (C : Type u) [_root_.CategoryTheory.Category.{v} C] [h : HomotopicalCategory C] :
    _root_.CategoryTheory.MorphismProperty C := h.weakEquivalences.morphisms

/-- Every category admits the maximal homotopical structure in which every morphism is weak. -/
@[instance_reducible]
def all (C : Type u) [_root_.CategoryTheory.Category.{v} C] : HomotopicalCategory C where
  weakEquivalences := WeakEquivalences.all C

end HomotopicalCategory

variable {D : Type u'} [_root_.CategoryTheory.Category.{v'} D]
variable [HomotopicalCategory C] [HomotopicalCategory D]

/-- A functor between homotopical categories is homotopical when it preserves weak equivalences
(FC03-C06-U028). -/
def IsHomotopical (F : C ⥤ D) : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y), HomotopicalCategory.W C f → HomotopicalCategory.W D (F.map f)

/-- The identity functor is homotopical for every chosen homotopical structure. -/
theorem isHomotopical_id : IsHomotopical (𝟭 C) := by
  intro X Y f hf
  simpa using hf

/-- A functor fails to be homotopical as soon as it sends one weak equivalence to a non-weak map.
This is the separating case for the functor definition. -/
theorem not_isHomotopical_of_map_not_weak (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)
    (hf : HomotopicalCategory.W C f) (hmap : ¬ HomotopicalCategory.W D (F.map f)) :
    ¬ IsHomotopical F := by
  intro hF
  exact hmap (hF f hf)

end LeanCategories.CategoryTheory

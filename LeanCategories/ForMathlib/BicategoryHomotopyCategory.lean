/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# The homotopy category of a bicategory

This file transcribes Kerodon Construction 2.2.8.12, tag `02AW`.  The objects of the
homotopy category are the objects of the bicategory, and its morphisms are isomorphism
classes of 1-morphisms.  Composition is induced by bicategorical composition; the
associator and unitors make the category laws hold after passing to isomorphism classes.

Equivalently, these isomorphism classes are the connected components of the hom-groupoids
of `Bicategory.Pith B`.

## References

* [Kerodon, Construction 2.2.8.12](https://kerodon.net/tag/02AW)
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.ForMathlib

universe w v u

/-- The homotopy category of a bicategory, with the same objects as the bicategory. -/
structure BicategoryHomotopyCategory (B : Type u) where
  /-- The underlying object of the bicategory. -/
  as : B

namespace BicategoryHomotopyCategory

variable (B : Type u) [Bicategory.{w, v} B]

/-- The isomorphism class of a 1-morphism in a bicategory. -/
def Hom (X Y : B) := Quotient (CategoryTheory.isIsomorphicSetoid (X ⟶ Y))

/-- The isomorphism class of a 1-morphism. -/
def classOf {X Y : B} (f : X ⟶ Y) : Hom B X Y :=
  Quotient.mk (CategoryTheory.isIsomorphicSetoid (X ⟶ Y)) f

def homComp {X Y Z : B} : Hom B X Y → Hom B Y Z → Hom B X Z :=
  Quotient.map₂
    (fun f g ↦ f ≫ g)
    fun f f' hf g g' hg ↦ by
    obtain ⟨hf⟩ := hf
    obtain ⟨hg⟩ := hg
    exact ⟨CategoryTheory.Bicategory.whiskerRightIso hf g ≪≫
      CategoryTheory.Bicategory.whiskerLeftIso f' hg⟩

instance categoryStruct : CategoryStruct (BicategoryHomotopyCategory B) where
  Hom X Y := Hom B X.as Y.as
  id X := classOf B (𝟙 X.as)
  comp := homComp B

instance category : Category (BicategoryHomotopyCategory B) where
  assoc f g h := by
    induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    induction h using Quotient.inductionOn
    exact Quotient.sound ⟨CategoryTheory.Bicategory.associator _ _ _⟩
  id_comp f := by
    induction f using Quotient.inductionOn
    exact Quotient.sound ⟨CategoryTheory.Bicategory.leftUnitor _⟩
  comp_id f := by
    induction f using Quotient.inductionOn
    exact Quotient.sound ⟨CategoryTheory.Bicategory.rightUnitor _⟩

@[simp]
theorem classOf_id (X : B) :
    classOf B (𝟙 X) = 𝟙 (BicategoryHomotopyCategory.mk X) := rfl

@[simp]
theorem classOf_comp {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    classOf B (f ≫ g) = homComp B (classOf B f) (classOf B g) := rfl

end BicategoryHomotopyCategory

end LeanCategories.ForMathlib

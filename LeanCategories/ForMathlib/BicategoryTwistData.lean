/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# Construction data for twisting a bicategory

Definition-level realization of Kerodon FC17-KER-U00322 (tag 009F).

A twisting cochain chooses an alternate composite for every composable pair of
1-morphisms together with an isomorphism from that composite to the original
one.  Kerodon's twist keeps objects, hom-categories, and identity 1-morphisms
unchanged, transports horizontal composition of 2-morphisms by conjugation,
and conjugates the unit and associativity constraints by the chosen
comparison isomorphisms.

This file records exactly those construction formulas.  Proving that they
satisfy the bicategory axioms, and hence packaging them as a `Bicategory`
instance, is result/proof work and is deliberately outside Sweep III.
-/

@[expose] public section

namespace LeanCategories.BicategoryTwist

open CategoryTheory
open CategoryTheory.Bicategory

universe w v u

variable {C : Type u} [CategoryTheory.Bicategory.{w, v} C]

/-- Kerodon's twisting-cochain datum: an alternate composite together with an
invertible comparison 2-cell to the original composite. -/
structure TwistingCochain (C : Type u) [CategoryTheory.Bicategory.{w, v} C] where
  comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z
  comparison {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    comp f g ≅ f ≫ g

namespace TwistingCochain

variable (T : TwistingCochain C)

/-- The twist has the same hom-categories as the original bicategory. -/
abbrev Hom (X Y : C) := X ⟶ Y

/-- The twist has the same identity 1-morphisms as the original bicategory. -/
abbrev id (X : C) : Hom X X := 𝟙 X

/-- Horizontal composition of 2-morphisms in the twist, obtained by
conjugating the original horizontal composite by the twisting cochain. -/
def horizontalComp {X Y Z : C} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    (γ : f ⟶ f') (δ : g ⟶ g') : T.comp f g ⟶ T.comp f' g' :=
  (T.comparison f g).hom ≫
    (γ ▷ g) ≫
    (f' ◁ δ) ≫
    (T.comparison f' g').inv

/-- Kerodon's unit constraint for the twist: compare the alternate composite
of the two identity 1-morphisms with the old composite, then apply the old
unit constraint. -/
def unitIso (X : C) : T.comp (𝟙 X) (𝟙 X) ≅ 𝟙 X :=
  T.comparison (𝟙 X) (𝟙 X) ≪≫ λ_ (𝟙 X)

/-- Kerodon's associativity constraint for the twist.  This is the displayed
five-step conjugation by the twisting cochain around the original
associator. -/
def associatorIso {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    T.comp (T.comp f g) h ≅ T.comp f (T.comp g h) :=
  T.comparison (T.comp f g) h ≪≫
    whiskerRightIso (T.comparison f g) h ≪≫
    α_ f g h ≪≫
    whiskerLeftIso f (T.comparison g h).symm ≪≫
    (T.comparison f (T.comp g h)).symm

end TwistingCochain

end LeanCategories.BicategoryTwist

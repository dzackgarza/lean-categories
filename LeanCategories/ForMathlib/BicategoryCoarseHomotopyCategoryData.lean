/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.ConnectedComponents

/-!
# Coarse homotopy category data of a bicategory

Definition-level realization of Kerodon Construction 2.2.8.2, tag 02AS.

For a bicategory B, the coarse homotopy category has the same objects and
hom-sets given by the connected components of the hom-categories. Composition
is induced by horizontal composition of 1-morphisms.

The last sentence is precisely where quotient descent enters. Sweep III
therefore records the object carrier, hom-set carrier, identity classes, and
the exact graph of composition. It does not select a representative-dependent
binary operation on connected components and does not install a Category
instance. Proving that the graph is total and single-valued, and then proving
the category laws from the bicategorical associator and unitors, is result
work.

This construction is distinct from Kerodon tag 02AW: the latter first takes
the locally groupoidal pith and hence uses isomorphism classes of 1-morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Bicategory

namespace LeanCategories.ForMathlib

universe w v u

variable (B : Type u) [Bicategory.{w, v} B]

/-- Object carrier of the coarse homotopy category. -/
structure BicategoryCoarseHomotopyObjectData where
  as : B

namespace BicategoryCoarseHomotopyObjectData

/-- Kerodon's coarse hom-set from X to Y: connected components of the
hom-category B(X,Y). -/
abbrev Hom (X Y : B) :=
  ConnectedComponents (X ⟶ Y)

/-- Class of a 1-morphism in the corresponding coarse hom-set. -/
def classOf {X Y : B} (f : X ⟶ Y) : Hom B X Y :=
  ConnectedComponents.mk f

/-- Identity class prescribed by Kerodon's construction. -/
def idData (X : B) : Hom B X X :=
  classOf B (𝟙 X)

/-- Exact graph of composition in the coarse homotopy category.

IsCompData a b c says that a, b, and c admit representatives f, g, and
f ≫ g respectively. Descent of horizontal composition along zigzag
connectedness is deliberately not proved here. -/
def IsCompData {X Y Z : B}
    (a : Hom B X Y) (b : Hom B Y Z) (c : Hom B X Z) : Prop :=
  ∃ (f : X ⟶ Y) (g : Y ⟶ Z),
    classOf B f = a ∧
    classOf B g = b ∧
    classOf B (f ≫ g) = c

/-- Raw construction package for Kerodon's coarse homotopy category.

It records only the data that can be stated before quotient descent. -/
structure StructureData where
  id : ∀ X : B, Hom B X X
  IsComp : ∀ {X Y Z : B}, Hom B X Y → Hom B Y Z → Hom B X Z → Prop

/-- The source-prescribed identity/composition graph data. -/
def structureData : StructureData B where
  id := idData B
  IsComp := IsCompData B

end BicategoryCoarseHomotopyObjectData

end LeanCategories.ForMathlib

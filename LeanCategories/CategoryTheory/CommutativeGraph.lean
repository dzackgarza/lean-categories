/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

open _root_.CategoryTheory

namespace LeanCategories.CategoryTheory

universe v u w

variable {C : Type u} [_root_.CategoryTheory.Category.{v} C]

/-- A directed graph displayed in a category: vertices are assigned objects and graph edges are
assigned morphisms with the corresponding endpoints (FC03-C01-U077). -/
structure DisplayedGraph where
  Vertex : Type w
  [quiver : _root_.Quiver.{w} Vertex]
  obj : Vertex → C
  map : ∀ {X Y : Vertex}, (X ⟶ Y) → (obj X ⟶ obj Y)

attribute [instance] DisplayedGraph.quiver

namespace DisplayedGraph

/-- Composite in the ambient category of the morphisms decorating a directed path. -/
def pathMap (D : DisplayedGraph (C := C)) {X : D.Vertex} :
    ∀ {Y : D.Vertex}, _root_.Quiver.Path X Y → (D.obj X ⟶ D.obj Y)
  | _, .nil => 𝟙 _
  | _, .cons p e => D.pathMap p ≫ D.map e

/-- A displayed directed graph is commutative when any two paths with common source and target
have equal composites (FC03-C01-U077). -/
def IsCommutative (D : DisplayedGraph (C := C)) : Prop :=
  ∀ {X Y : D.Vertex} (p q : _root_.Quiver.Path X Y), D.pathMap p = D.pathMap q

/-- A displayed graph in a thin category is automatically commutative; this supplies the basic
positive model for the source definition. -/
theorem isCommutative_of_subsingleton_hom (D : DisplayedGraph (C := C))
    (h : ∀ X Y : C, Subsingleton (X ⟶ Y)) : D.IsCommutative := by
  intro X Y p q
  exact @Subsingleton.elim _ (h (D.obj X) (D.obj Y)) _ _

/-- Two parallel displayed paths with different composites witness failure of commutativity. -/
theorem not_isCommutative_of_pathMap_ne (D : DisplayedGraph (C := C))
    {X Y : D.Vertex} (p q : _root_.Quiver.Path X Y) (h : D.pathMap p ≠ D.pathMap q) :
    ¬ D.IsCommutative := by
  intro hD
  exact h (hD p q)

end DisplayedGraph

end LeanCategories.CategoryTheory

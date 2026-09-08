/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Category.Quiv

@[expose] public section

open _root_.CategoryTheory

namespace LeanCategories.CategoryTheory

/-- The two vertices underlying Riehl's walking/free arrow (FC03-C01-U056). -/
inductive WalkingArrowVertex
  | zero
  | one
deriving DecidableEq, Repr

namespace WalkingArrowVertex

/-- The one generating edge of the walking-arrow quiver. -/
inductive Edge : WalkingArrowVertex → WalkingArrowVertex → Type
  | arrow : Edge .zero .one

instance : _root_.Quiver WalkingArrowVertex where
  Hom := Edge

end WalkingArrowVertex

/-- Riehl's walking/free arrow: the free category on the quiver with two vertices and one edge.
The freeness is Mathlib's path-category universal property `CategoryTheory.Quiv.pathsEquiv`.
(FC03-C01-U056) -/
abbrev WalkingArrow := _root_.CategoryTheory.Paths WalkingArrowVertex

namespace WalkingArrow

/-- The generating one-edge path of the walking-arrow category. -/
def generator : _root_.Quiver.Path WalkingArrowVertex.zero WalkingArrowVertex.one :=
  _root_.Quiver.Hom.toPath WalkingArrowVertex.Edge.arrow

universe v u

variable {C : Type u} [_root_.CategoryTheory.Category.{v} C]

/-- Universal property of the walking/free arrow: functors from it are exactly prefunctors from
its one-edge generating quiver. -/
def universalProperty :
    (WalkingArrow ⥤ C) ≃ (WalkingArrowVertex ⥤q C) :=
  _root_.CategoryTheory.Quiv.pathsEquiv

/-- There is no path in the generating quiver from `one` back to `zero`; hence the walking
arrow is not the walking isomorphism. -/
theorem noPathOneZero (p : _root_.Quiver.Path WalkingArrowVertex.one WalkingArrowVertex.zero) :
    False := by
  cases p with
  | cons p e => cases e


end WalkingArrow

/-- The walking arrow is not a groupoid: its generating arrow has no inverse. -/
public theorem walkingArrow_not_isGroupoid : ¬ _root_.CategoryTheory.IsGroupoid WalkingArrow := by
  intro h
  let f : @Quiver.Hom WalkingArrow
      (_root_.CategoryTheory.Paths.categoryPaths WalkingArrowVertex).toQuiver
      WalkingArrowVertex.zero WalkingArrowVertex.one := WalkingArrow.generator
  letI : _root_.CategoryTheory.IsIso f := h.all_isIso f
  let g := _root_.CategoryTheory.inv f
  exact WalkingArrow.noPathOneZero g


end LeanCategories.CategoryTheory

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Groupoid
public import LeanCategories.CategoryTheory.WalkingArrow

@[expose] public section

open _root_.CategoryTheory

namespace LeanCategories.CategoryTheory

universe v u w

/-- A category is essentially discrete when it is equivalent to a discrete category
(FC03-C01-U074). -/
def EssentiallyDiscrete (C : Type u) [_root_.CategoryTheory.Category.{v} C] : Prop :=
  ∃ α : Type w, Nonempty (C ≌ Discrete α)

/-- Discrete categories are essentially discrete: the basic positive example for FC03-C01-U074. -/
theorem essentiallyDiscrete_discrete (α : Type w) :
    EssentiallyDiscrete.{w,w,w} (Discrete α) :=
  ⟨α, ⟨_root_.CategoryTheory.Equivalence.refl⟩⟩

/-- Every essentially discrete category is a groupoid, since an equivalence to a discrete category
reflects invertibility. -/
theorem EssentiallyDiscrete.isGroupoid {C : Type u} [_root_.CategoryTheory.Category.{v} C]
    (h : EssentiallyDiscrete.{v,u,w} C) : _root_.CategoryTheory.IsGroupoid C := by
  rcases h with ⟨α, ⟨e⟩⟩
  constructor
  intro X Y f
  exact _root_.CategoryTheory.isIso_of_fully_faithful e.functor f

/-- The walking arrow is not essentially discrete: every essentially discrete category is a
groupoid, while `WalkingArrow.not_isGroupoid` gives the separating counterexample. -/
theorem not_essentiallyDiscrete_walkingArrow :
    ¬ EssentiallyDiscrete.{0,0,0} WalkingArrow := by
  intro h
  exact walkingArrow_not_isGroupoid h.isGroupoid

end LeanCategories.CategoryTheory

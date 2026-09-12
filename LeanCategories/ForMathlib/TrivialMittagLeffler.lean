/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.CofilteredSystem

/-!
# Trivial Mittag--Leffler systems

Weibel, *An Introduction to Homological Algebra*, Definition 3.5.6 (FC05-C03-U052).
Mathlib's `Functor.IsMittagLeffler` already records stabilization of images for a functor to
`Type`. Weibel also names the stronger *trivial Mittag--Leffler* condition for an inverse system
of abelian groups: sufficiently far transition maps into every fixed stage are zero.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

universe u v

variable {J : Type u} [Category* J]

/-- Weibel's trivial Mittag--Leffler condition for a diagram of additive commutative groups.

For every stage `j`, some transition map from a later stage into `j` is the zero morphism. For a
countable inverse tower indexed by `ℕᵒᵖ`, this says exactly that for every `n` there is a
sufficiently large `m ≥ n` for which the transition `A_m ⟶ A_n` is zero. -/
def IsTriviallyMittagLeffler (F : J ⥤ AddCommGrpCat.{v}) : Prop :=
  ∀ j : J, ∃ (i : J) (f : i ⟶ j), F.map f = 0

/-- A trivially Mittag--Leffler system is Mittag--Leffler after forgetting to sets. -/
theorem IsTriviallyMittagLeffler.isMittagLeffler {F : J ⥤ AddCommGrpCat.{v}}
    (h : F.IsTriviallyMittagLeffler) :
    (F ⋙ forget AddCommGrpCat).IsMittagLeffler := by
  intro j
  obtain ⟨i, f, hf⟩ := h j
  refine ⟨i, f, ?_⟩
  intro k g x hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(0 : F.obj k), ?_⟩
  change F.map g 0 = F.map f y
  rw [hf]
  simp

end CategoryTheory.Functor

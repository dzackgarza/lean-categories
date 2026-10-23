/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Category.PartOrd
public import Mathlib.Order.Grade

/-!
# Finite graded posets

Mathlib's `GradeOrder` retains the selected grade and its covering relation.
This category fixes an integer grade so that the empty face of an abstract
polytope may have grade `-1`. Its maps preserve both order and grade.
The construction combines `Mathlib.Order.Grade` with Mathlib's `PartOrd`
category and restricts its arrows to grade-preserving maps.
-/

@[expose] public section

open CategoryTheory

universe u

/-- A finite partially ordered set with a selected integer grading. -/
structure FiniteGradedPoset where
  carrier : Type u
  [order : PartialOrder carrier]
  [finite : Fintype carrier]
  [grading : GradeOrder ℤ carrier]

attribute [instance] FiniteGradedPoset.order FiniteGradedPoset.finite
  FiniteGradedPoset.grading

namespace FiniteGradedPoset

instance : CoeSort FiniteGradedPoset.{u} (Type u) := ⟨carrier⟩

/-- A rank-preserving monotone map between finite graded posets. -/
@[ext]
structure Hom (P Q : FiniteGradedPoset.{u}) where
  toOrderHom : P →o Q
  grade_eq : ∀ x : P, grade ℤ (toOrderHom x) = grade ℤ x

instance : Category FiniteGradedPoset.{u} where
  Hom := Hom
  id P := ⟨OrderHom.id, fun _ => rfl⟩
  comp f g := ⟨g.toOrderHom.comp f.toOrderHom, fun x =>
    (g.grade_eq (f.toOrderHom x)).trans (f.grade_eq x)⟩

/-- Forget the selected grading and finiteness, retaining the order map. -/
def forget : FiniteGradedPoset.{u} ⥤ PartOrd.{u} where
  obj P := PartOrd.of P
  map f := PartOrd.ofHom f.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

end FiniteGradedPoset

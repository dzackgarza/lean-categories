/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Opposites

@[expose] public section

open _root_.CategoryTheory

namespace LeanCategories.CategoryTheory

open _root_.CategoryTheory.Functor

universe vC uC vD uD vE uE

variable {C : Type uC} [_root_.CategoryTheory.Category.{vC} C]
variable {D : Type uD} [_root_.CategoryTheory.Category.{vD} D]
variable {E : Type uE} [_root_.CategoryTheory.Category.{vE} E]

/-- Riehl's definition of a pointwise right Kan extension: a right Kan extension is pointwise
when every covariant representable `E(e,-)` preserves it (FC03-C06-U020).

This deliberately differs from Mathlib's `RightExtension.IsPointwiseRightKanExtension`, whose
*definition* is the comma-limit criterion. Riehl proves the equivalence later in Theorem 6.3.7. -/
def IsRiehlPointwiseRightKanExtension {K : C ⥤ D} {F : C ⥤ E} (R : D ⥤ E)
    (ε : K ⋙ R ⟶ F) [R.IsRightKanExtension ε] : Prop :=
  ∀ e : E,
    (R ⋙ coyoneda.obj (Opposite.op e)).IsRightKanExtension
      ((Functor.associator K R (coyoneda.obj (Opposite.op e))).inv ≫
        whiskerRight ε (coyoneda.obj (Opposite.op e)))

/-- Riehl's definition of a pointwise left Kan extension: first pass the left Kan extension to
opposite categories, which turns it into a right Kan extension, and then require preservation by
every contravariant representable `E(-,e)` (FC03-C06-U021).

Again this is kept distinct from Mathlib's comma-colimit definition; their equivalence is theorem
content, not part of this source definition. -/
def IsRiehlPointwiseLeftKanExtension {K : C ⥤ D} {F : C ⥤ E} (L : D ⥤ E)
    (η : F ⟶ K ⋙ L) [L.IsLeftKanExtension η] : Prop :=
  ∀ e : E,
    (L.op ⋙ yoneda.obj e).IsRightKanExtension
      ((Functor.associator K.op L.op (yoneda.obj e)).inv ≫
        whiskerRight ((Functor.opComp K L).inv ≫ NatTrans.op η) (yoneda.obj e))

/-- Identity right Kan extensions are pointwise in Riehl's sense: the basic positive model for
FC03-C06-U020. -/
theorem riehlPointwiseRight_id (F : C ⥤ E) :
    IsRiehlPointwiseRightKanExtension F F.leftUnitor.hom := by
  intro e
  infer_instance

/-- A representable that fails to preserve the given right Kan extension is a separating witness
against Riehl pointwiseness. -/
theorem not_riehlPointwiseRight_of_not_preserved {K : C ⥤ D} {F : C ⥤ E} (R : D ⥤ E)
    (ε : K ⋙ R ⟶ F) [R.IsRightKanExtension ε] (e : E)
    (h : ¬ (R ⋙ coyoneda.obj (Opposite.op e)).IsRightKanExtension
      ((Functor.associator K R (coyoneda.obj (Opposite.op e))).inv ≫
        whiskerRight ε (coyoneda.obj (Opposite.op e)))) :
    ¬ IsRiehlPointwiseRightKanExtension R ε := by
  intro hp
  exact h (hp e)

/-- Identity left Kan extensions are pointwise in Riehl's sense: the dual positive model for
FC03-C06-U021. -/
theorem riehlPointwiseLeft_id (F : C ⥤ E) :
    IsRiehlPointwiseLeftKanExtension F F.leftUnitor.inv := by
  intro e
  infer_instance

/-- A contravariant representable that fails the opposite-category right-Kan test is a separating
witness against Riehl pointwiseness on the left. -/
theorem not_riehlPointwiseLeft_of_not_preserved {K : C ⥤ D} {F : C ⥤ E} (L : D ⥤ E)
    (η : F ⟶ K ⋙ L) [L.IsLeftKanExtension η] (e : E)
    (h : ¬ (L.op ⋙ yoneda.obj e).IsRightKanExtension
      ((Functor.associator K.op L.op (yoneda.obj e)).inv ≫
        whiskerRight ((Functor.opComp K L).inv ≫ NatTrans.op η) (yoneda.obj e))) :
    ¬ IsRiehlPointwiseLeftKanExtension L η := by
  intro hp
  exact h (hp e)

end LeanCategories.CategoryTheory

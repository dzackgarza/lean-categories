/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryGraph.Core.CategoricalPullback
public import LeanCategories.CategoryGraph.Core.Ids
public import LeanCategories.CategoryGraph.Core.Linters

@[expose] public section

/-!
# Classifier reindexing

This file exposes reindexing data and its identity and composition coherences.
It does not package classifiers into a strict category. Such packaging needs
actual comparison 2-cells and their bicategorical coherence.
-/

namespace CategoryGraph.ClassifierReindexing

open CategoryTheory

universe uObj uHom

set_option linter.checkUnivs false

/-- Reindex a classifier along a functor into its host. -/
noncomputable def reindex {C D : ObjCat.{uObj, uHom}} (F : D ⟶ C) (A : Classifier C) :
    Reindexed F A :=
  Classifier.reindex F A

/-- Projection from a reindexed total category to its new host. -/
def baseProjection {C D : ObjCat.{uObj, uHom}} {F : D ⟶ C} {A : Classifier C}
    (R : Reindexed F A) : R.total ⟶ D :=
  R.baseProjection

/-- Projection from a reindexed total category to the original classifier total. -/
def classifierProjection {C D : ObjCat.{uObj, uHom}} {F : D ⟶ C} {A : Classifier C}
    (R : Reindexed F A) : R.total ⟶ A.total :=
  R.axiomProjection

/-- The canonical comparison square for a reindexing. -/
@[reducible] def square {C D : ObjCat.{uObj, uHom}} {F : D ⟶ C} {A : Classifier C}
    (R : Reindexed F A) :=
  R.square

/-- Identity reindex coherence on the underlying categories. -/
structure ReindexIdIso {C : ObjCat.{uObj, uHom}} (A : Classifier C) where
  equiv : (Classifier.reindex (𝟙 C) A).total ≌ A.total

/-- Composition reindex coherence on the underlying categories. -/
structure ReindexCompIso {B C D : ObjCat.{uObj, uHom}} (G : D ⟶ C) (F : C ⟶ B)
    (A : Classifier B) where
  equiv :
    (Classifier.reindex (G ≫ F) A).total ≌
      (Classifier.reindex G (Classifier.reindex F A).asClassifier).total

end CategoryGraph.ClassifierReindexing

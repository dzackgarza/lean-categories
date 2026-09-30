/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryTheory.OneCat.Universes
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

/-!
# Classifier

The fundamental object: for an axiom/structure `A` on `C`,

\[
A = (\iota_A : C.A \to C).
\]

Property / structure / stuff are consequences of fullness and faithfulness of
`forget`, not an authored enum. The manifest may report `property` only when a
proof declaration supports it.
-/

namespace LeanCategories

open CategoryTheory

universe uObj uHom

/-- Minimal classifier datum on a host category. -/
structure Classifier (C : ObjCat.{uObj, uHom}) where
  total : ObjCat.{uObj, uHom}
  forget : total ⟶ C

/-- The classifier of a property `P` of objects: its total is Mathlib's full subcategory on `P`,
its forgetful functor the inclusion `P.ι`. -/
def Classifier.ofProperty {C : ObjCat.{uObj, uHom}} (P : ObjectProperty C) : Classifier C where
  total := Cat.of P.FullSubcategory
  forget := P.ι.toCatHom

/-- Property classifier: full, faithful, and replete (when repleteness is available).
Manifest `kind := property` requires these proofs — never an unchecked tag. -/
structure PropertyClassifier (C : ObjCat.{uObj, uHom}) extends Classifier C where
  full : forget.toFunctor.Full
  faithful : forget.toFunctor.Faithful

/-- Structure classifier: faithful forgetful (not necessarily full). -/
structure StructureClassifier (C : ObjCat.{uObj, uHom}) extends Classifier C where
  faithful : forget.toFunctor.Faithful

end LeanCategories

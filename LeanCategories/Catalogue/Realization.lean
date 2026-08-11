module

public import LeanCategories.CategoryTheory.OneCat.Classifier
public import LeanCategories.Catalogue.Syntax

@[expose] public section

/-!
# Typed catalogue realizations

These witnesses connect symbolic expressions to actual categories, classifiers,
families, and functors. Imported domain modules provide the witnesses locally.
-/

namespace LeanCategories

open CategoryTheory

universe uObj uHom uParam

/-- An actual category assigned to a symbolic category expression. -/
structure CategoryRealization (expression : CategoryExpr)
    (category : ObjCat.{uObj, uHom}) where

/-- An actual parameterized family assigned to a family identifier. -/
structure CategoryFamilyRealization (identifier : CategoryFamilyId) where
  Parameter : Type uParam
  fibre : Parameter → ObjCat.{uObj, uHom}

/-- An actual classifier assigned to a symbolic host and classifier identifier. -/
structure ClassifierRealization (host : CategoryExpr) (identifier : ClassifierId)
    (category : ObjCat.{uObj, uHom}) (classifier : Classifier category) where

/-- An actual functor assigned to a typed symbolic functor expression. -/
structure FunctorRealization {source target : CategoryExpr}
    (expression : FunctorExpr source target)
    (sourceCategory targetCategory : ObjCat.{uObj, uHom})
    (functor : sourceCategory ⟶ targetCategory) where

end LeanCategories

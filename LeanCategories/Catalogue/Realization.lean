module

public import LeanCategories.CategoryTheory.OneCat.Classifier
public import LeanCategories.Catalogue.Syntax
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Discrete.Basic

@[expose] public section

/-!
# Typed catalogue realizations

These witnesses connect symbolic expressions to actual categories, classifiers,
families, and functors. Imported domain modules provide the witnesses locally.
-/

namespace LeanCategories

open CategoryTheory

universe u

namespace CategoryFamilySchema

@[reducible] def Parameters : CategoryFamilySchema → Type (u + 1)
  | .ring => RingCat.{u}
  | .commRing => Discrete (CommRingCat.{u})
  | .commRingModule => Discrete (Σ R : CommRingCat.{u}, ModuleCat.{u} R)

end CategoryFamilySchema

universe uObj uHom uParam uParamHom

attribute [local simp] Bicategory.Strict.leftUnitor_eqToIso
  Bicategory.Strict.rightUnitor_eqToIso Bicategory.Strict.associator_eqToIso

/-- An actual parameterized family assigned to a family identifier. -/
structure CategoryFamilyRealization (identifier : CategoryFamilyId)
    (schema : CategoryFamilySchema) where
  [parameterCategory : Category.{uParamHom} schema.Parameters.{uParam}]
  transport :
    Pseudofunctor (LocallyDiscrete schema.Parameters.{uParam}ᵒᵖ)
      (Cat.{uHom, max uObj uHom})

/-- A family indexed by a discrete parameter object, with no transport beyond equality. -/
noncomputable def discreteFamilyTransport {P : Type uParam}
    (fibre : P → ObjCat.{uObj, uHom}) :
    Pseudofunctor (LocallyDiscrete (Discrete P)ᵒᵖ)
      (Cat.{uHom, max uObj uHom}) :=
  LocallyDiscrete.mkPseudofunctor
    (fun parameter => fibre parameter.unop.as)
    (fun {source target} map => eqToHom
      (congrArg fibre (Discrete.eq_of_hom map.unop).symm))
    (fun _ => eqToIso (by simp))
    (fun _ _ => eqToIso (by simp))
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)

/-- The selected fibre is the pseudofunctor value at the opposite parameter. -/
def CategoryFamilyRealization.fibre {identifier : CategoryFamilyId}
    {schema : CategoryFamilySchema}
    (realization : CategoryFamilyRealization identifier schema)
    (parameter : schema.Parameters) : ObjCat.{uObj, uHom} :=
  letI := realization.parameterCategory
  realization.transport.obj (.mk (Opposite.op parameter))

/-- A typed witness that a named category is a selected fibre of a family. -/
structure CategoryFamilyFibreWitness (category : ObjCat.{uObj, uHom})
    {identifier : CategoryFamilyId} {schema : CategoryFamilySchema}
    (realization : CategoryFamilyRealization.{uObj, uHom, uParam, uParamHom} identifier schema) where
  parameter : schema.Parameters
  category_eq : category = realization.fibre parameter

/-- Existential package for a fibre witness with its exact realization index. -/
inductive SomeCategoryFamilyFibreWitness (category : ObjCat.{uObj, uHom}) where
  | mk {identifier : CategoryFamilyId} {schema : CategoryFamilySchema}
      (realization : CategoryFamilyRealization.{uObj, uHom, uParam, uParamHom} identifier schema)
      (witness : CategoryFamilyFibreWitness category realization)

/-- An actual category assigned to a symbolic category expression. -/
structure CategoryRealization (expression : CategoryExpr)
    (category : ObjCat.{uObj, uHom}) where
  familyFibre : Option
      (SomeCategoryFamilyFibreWitness.{uObj, uHom, uParam, uParamHom} category) := none

/-- An actual classifier assigned to a symbolic host and classifier identifier. -/
structure ClassifierRealization (host : CategoryExpr) (identifier : ClassifierId)
    (category : ObjCat.{uObj, uHom}) (classifier : Classifier category) where

/-- An actual functor assigned to a typed symbolic functor expression. -/
structure FunctorRealization {source target : CategoryExpr}
    (expression : FunctorExpr source target)
    (sourceCategory targetCategory : ObjCat.{uObj, uHom})
    (functor : sourceCategory ⟶ targetCategory) where

end LeanCategories

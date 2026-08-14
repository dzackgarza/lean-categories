module

public import LeanCategories.CategoryTheory.OneCat.Classifier
public import LeanCategories.Catalogue.Syntax
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
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
end CategoryFamilySchema

universe uObj uHom uParam uParamHom
universe uHostParam uHostParamHom uTotalParam uTotalParamHom
universe uSourceParam uSourceParamHom uTargetParam uTargetParamHom

attribute [local simp] Bicategory.Strict.leftUnitor_eqToIso
  Bicategory.Strict.rightUnitor_eqToIso Bicategory.Strict.associator_eqToIso

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

/-- An actual parameterized family assigned to a family identifier. -/
structure CategoryFamilyRealization (identifier : CategoryFamilyId)
    (schema : CategoryFamilySchema) where
  [parameterCategory : Category.{uParamHom} schema.Parameters.{uParam}]
  transport :
    Pseudofunctor (LocallyDiscrete schema.Parameters.{uParam}ᵒᵖ)
      (Cat.{uHom, max uObj uHom})
  /-- The registered semantic kind of this transport. -/
  transportSemantics : CategoryFamilyTransportSemantics

/-- The selected fibre is the pseudofunctor value at the opposite parameter. -/
def CategoryFamilyRealization.fibre {identifier : CategoryFamilyId}
    {schema : CategoryFamilySchema}
    (realization : CategoryFamilyRealization identifier schema)
    (parameter : schema.Parameters) : ObjCat.{uObj, uHom} :=
  letI := realization.parameterCategory
  realization.transport.obj (.mk (Opposite.op parameter))

/-- The canonical equality-only transport for commutative-ring fibres. -/
noncomputable def CategoryFamilyRealization.canonicalDiscreteCommRingTransport
    {identifier : CategoryFamilyId}
    (realization : CategoryFamilyRealization.{uObj, uHom, uParam, uParam + 1}
      identifier .commRing) :
    Pseudofunctor (LocallyDiscrete (Discrete (CommRingCat.{uParam}))ᵒᵖ)
      (Cat.{uHom, max uObj uHom}) :=
  discreteFamilyTransport.{uObj, uHom, uParam + 1}
    (fun parameter => realization.fibre ⟨parameter⟩)

/-- The canonical equality-only transport for commutative-ring module fibres. -/
noncomputable def CategoryFamilyRealization.canonicalDiscreteCommRingModuleTransport
    {identifier : CategoryFamilyId}
    (realization : CategoryFamilyRealization.{uObj, uHom, uParam, uParam + 1}
      identifier .commRingModule) :
    Pseudofunctor
      (LocallyDiscrete
        (Discrete (Σ R : CommRingCat.{uParam}, ModuleCat.{uParam} R))ᵒᵖ)
      (Cat.{uHom, max uObj uHom}) :=
  discreteFamilyTransport.{uObj, uHom, uParam + 1}
    (fun parameter => realization.fibre ⟨parameter⟩)

/-- Typed quotation of the concrete parameter represented by a family application. -/
inductive CategoryFamilyParameterQuotation :
    (schema : CategoryFamilySchema) → Array ParameterExpr → schema.Parameters → Prop
  | ringR (R : RingCat.{u}) :
      CategoryFamilyParameterQuotation .ring #[.variable ParameterId.r] R
  | ringS (S : RingCat.{u}) :
      CategoryFamilyParameterQuotation .ring #[.variable ParameterId.s] S
  | commRingR (R : CommRingCat.{u}) :
      CategoryFamilyParameterQuotation .commRing #[.variable ParameterId.r] ⟨R⟩
  | commRingS (S : CommRingCat.{u}) :
      CategoryFamilyParameterQuotation .commRing #[.variable ParameterId.s] ⟨S⟩
  | commRingModuleRW (R : CommRingCat.{u}) (W : ModuleCat.{u} R) :
      CategoryFamilyParameterQuotation .commRingModule
        #[.variable ParameterId.r, .variable ParameterId.w] ⟨R, W⟩
  | commRingModuleSW (S : CommRingCat.{u}) (W : ModuleCat.{u} S) :
      CategoryFamilyParameterQuotation .commRingModule
        #[.variable ParameterId.s, .variable ParameterId.w] ⟨S, W⟩
  | commRingModuleRWPrime (R : CommRingCat.{u}) (W : ModuleCat.{u} R) :
      CategoryFamilyParameterQuotation .commRingModule
        #[.variable ParameterId.r, .variable ParameterId.wPrime] ⟨R, W⟩
  | commRingModuleSWPrime (S : CommRingCat.{u}) (W : ModuleCat.{u} S) :
      CategoryFamilyParameterQuotation .commRingModule
        #[.variable ParameterId.s, .variable ParameterId.wPrime] ⟨S, W⟩
  | commRingModuleTensorProduct (R S W : Type u) [CommRing R] [CommRing S]
      [Algebra R S] [AddCommGroup W] [Module R W] :
      CategoryFamilyParameterQuotation .commRingModule
        #[.variable ParameterId.s,
          .apply3 ParameterOperationId.tensorProduct
            (.variable ParameterId.r) (.variable ParameterId.s) (.variable ParameterId.w)]
        ⟨CommRingCat.of S, ModuleCat.of S (TensorProduct R S W)⟩

/-- A typed witness that a named category is a selected fibre of a family. -/
structure CategoryFamilyFibreWitness (category : ObjCat.{uObj, uHom})
    {identifier : CategoryFamilyId} {schema : CategoryFamilySchema}
    (realization : CategoryFamilyRealization.{uObj, uHom, uParam, uParamHom} identifier schema)
    {arguments : Array ParameterExpr} where
  parameter : schema.Parameters
  parameterQuotation : CategoryFamilyParameterQuotation schema arguments parameter
  category_eq : category = realization.fibre parameter

def CategoryFamilyFibreWitness.arguments {category : ObjCat.{uObj, uHom}}
    {identifier : CategoryFamilyId} {schema : CategoryFamilySchema}
    {realization : CategoryFamilyRealization.{uObj, uHom, uParam, uParamHom} identifier schema}
    {arguments : Array ParameterExpr}
    (_witness : CategoryFamilyFibreWitness category realization (arguments := arguments)) :
    Array ParameterExpr := arguments

/-- Existential package for a fibre witness with its exact realization index. -/
inductive SomeCategoryFamilyFibreWitness (category : ObjCat.{uObj, uHom}) where
  | mk {identifier : CategoryFamilyId} {schema : CategoryFamilySchema}
      (realization : CategoryFamilyRealization.{uObj, uHom, uParam, uParamHom} identifier schema)
      {arguments : Array ParameterExpr}
      (witness : CategoryFamilyFibreWitness category realization (arguments := arguments))

/-- An actual category assigned to a symbolic category expression. -/
structure CategoryRealization (expression : CategoryExpr)
    (category : ObjCat.{uObj, uHom}) where
  familyFibre : Option
      (SomeCategoryFamilyFibreWitness.{uObj, uHom, uParam, uParamHom} category) := none

/-- An actual classifier assigned to a symbolic host and classifier identifier. -/
structure ClassifierRealization (host : CategoryExpr) (identifier : ClassifierId)
    (category : ObjCat.{uObj, uHom}) (classifier : Classifier category) where
  hostRealization :
    CategoryRealization.{uObj, uHom, uHostParam, uHostParamHom} host category
  totalRealization :
    CategoryRealization.{uObj, uHom, uTotalParam, uTotalParamHom}
      (.classifierTotal identifier) classifier.total

/-- An actual functor assigned to a typed symbolic functor expression. -/
structure FunctorRealization {source target : CategoryExpr}
    (expression : FunctorExpr source target)
    (sourceCategory targetCategory : ObjCat.{uObj, uHom})
    (functor : sourceCategory ⟶ targetCategory) where
  sourceRealization :
    CategoryRealization.{uObj, uHom, uSourceParam, uSourceParamHom} source sourceCategory
  targetRealization :
    CategoryRealization.{uObj, uHom, uTargetParam, uTargetParamHom} target targetCategory

end LeanCategories

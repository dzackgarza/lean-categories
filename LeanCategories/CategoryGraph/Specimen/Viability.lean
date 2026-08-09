/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryGraph.Core.StructuralMap
public import LeanCategories.CategoryGraph.Categories.Algebra.Rings
public import LeanCategories.CategoryGraph.ForMathlib.CategoricalPullback
public import LeanCategories.CategoryGraph.Registry.Entry
public import LeanCategories.CategoryGraph.Realization.Mathlib.Atomic
public import LeanCategories.CategoryGraph.Specimen.ViabilityData
public meta import LeanCategories.CategoryGraph.Specimen.ViabilityData
public meta import LeanCategories.CategoryGraph.Core.Expr
public meta import LeanCategories.CategoryGraph.Core.Ids
public meta import LeanCategories.CategoryGraph.Core.StructuralMap
public meta import LeanCategories.CategoryGraph.Core.Normalize
public meta import LeanCategories.CategoryGraph.Categories.Algebra.Magmas
public meta import LeanCategories.CategoryGraph.Categories.Algebra.Rings
public meta import LeanCategories.CategoryGraph.Registry.Extension




@[expose] public section

/-!
# Viability specimen — symbolic specification

Exercises: foundations, magma tower, two-operation rings, parameterized modules,
remote Finite, implicit Rings.Graded.Finite, opaque host, alias CRings.
-/

namespace CategoryGraph.Specimen

open CategoryGraph

/-! ## Classifier hosts -/

def specimenHosts : ClassifierHostTable where
  hostOf
    | ⟨"clf.sets.finite"⟩ | ⟨"clf.sets.graded"⟩ | ⟨"clf.sets.binary_operation"⟩ =>
        some CategoryId.sets
    | ⟨"clf.magmas.associative"⟩ | ⟨"clf.magmas.commutative"⟩
    | ⟨"clf.magmas.unital"⟩
    | ⟨"clf.magmas.additive"⟩ | ⟨"clf.magmas.multiplicative"⟩ =>
        some CategoryId.magmas
    | ⟨"clf.magmas.inverse"⟩ => some CategoryId.unitalMagmas
    | ⟨"clf.magmaswithtwooperations.distributive"⟩ =>
        some CategoryId.magmasWithTwoOperations
    | ⟨"clf.division"⟩ =>
        some CategoryId.rings
    | ⟨"clf.modules_free"⟩ | ⟨"clf.modules_finitelygenerated"⟩
    | ⟨"clf.modules_finiterank"⟩ =>
        some CategoryId.modulesR
    | _ => none

def specimenAliases : AliasTable where
  canonicalOf
    | ⟨"cat.crings"⟩ => some CategoryId.commutativeRings
    | _ => none

/-! ## Named expressions (canonical bodies) -/

/-- The actual identity functor on the realized Sets specimen. -/
noncomputable def specimenSetsIdentity :
    Normalized.Sets Realization.Mathlib.atomicModel.{0} ⟶
      Normalized.Sets Realization.Mathlib.atomicModel.{0} :=
  CategoryTheory.CategoryStruct.id _

/-- The actual Sets declaration is certified against the symbolic node it realizes. -/
noncomputable def specimenSetsRealization :
    CategoryRealization Realization.Mathlib.atomicModel.{0}
      Realization.Mathlib.specimenRingBinding (FunctorSemantics.empty _)
      exprSets (Normalized.Sets Realization.Mathlib.atomicModel) := by
  refine ⟨Normalized.Sets Realization.Mathlib.atomicModel, ?_, CategoryTheory.Equivalence.refl⟩
  exact Realization.Mathlib.evalAtom_sets

/-- The actual semantic binding for the registered Sets identity functor. -/
noncomputable def specimenFunctorSemantics :
    FunctorSemantics Realization.Mathlib.atomicModel.{0} where
  named id :=
    if id == FunctorId.mk "fun.sets.identity" then
      some ⟨Normalized.Sets Realization.Mathlib.atomicModel, Normalized.Sets Realization.Mathlib.atomicModel,
        specimenSetsIdentity⟩
    else none
  refinement _ := none
  opaquePort _ := none
  theoremInclusion _ := none
  finiteLimitLift _ := none
  constructorMap _ := none

/-- The actual Sets identity is certified against its typed symbolic functor. -/
theorem specimenSetsIdentityRealization :
    FunctorRealization Realization.Mathlib.atomicModel.{0}
      Realization.Mathlib.specimenRingBinding specimenFunctorSemantics
      exprSetsIdentity
      ⟨Normalized.Sets Realization.Mathlib.atomicModel,
        Normalized.Sets Realization.Mathlib.atomicModel, specimenSetsIdentity⟩ := by
  constructor
  simp [evalFunctor, exprSetsIdentity, exprSets, specimenFunctorSemantics,
    specimenSetsIdentity, evalCategory, Realization.Mathlib.evalAtom_sets]

/-- The registry-reference form evaluates through the same actual functor binding. -/
example :
    (evalCategory Realization.Mathlib.atomicModel.{0} Realization.Mathlib.specimenRingBinding
      specimenFunctorSemantics exprSetsIdentityPullback).isSome = true := by
  simp [evalCategory, exprSetsIdentityPullback, exprSets, specimenFunctorSemantics,
    EvaluatedFunctor.pullbackCategory]

example :
    (evalFunctor Realization.Mathlib.atomicModel.{0} Realization.Mathlib.specimenRingBinding
      specimenFunctorSemantics exprRegisteredSetsIdentity).isSome = true := by
  simp [evalFunctor, validateFunctor, evalCategory, exprSets, exprRegisteredSetsIdentity,
    specimenFunctorSemantics]

example :
    (evalFunctor Realization.Mathlib.atomicModel.{0} Realization.Mathlib.specimenRingBinding
      specimenFunctorSemantics (.compose (.identity exprSets) (.identity exprSets))).isSome = true := by
  simp [evalFunctor, validateFunctor, evalCategory, exprSets, specimenFunctorSemantics,
    EvaluatedFunctor.compose]

example :
    (evalClassifier Realization.Mathlib.atomicModel.{0} Realization.Mathlib.specimenRingBinding
      exprSets ClassifierId.setsFinite).isSome = true := by
  have associative : ClassifierId.setsFinite ≠ ClassifierId.magmasAssociative := by decide
  have commutative : ClassifierId.setsFinite ≠ ClassifierId.magmasCommutative := by decide
  have unital : ClassifierId.setsFinite ≠ ClassifierId.magmasUnital := by decide
  have inverse : ClassifierId.setsFinite ≠ ClassifierId.magmasInverse := by decide
  have additive : ClassifierId.setsFinite ≠ ClassifierId.magmasAdditive := by decide
  have multiplicative : ClassifierId.setsFinite ≠ ClassifierId.magmasMultiplicative := by decide
  have division : ClassifierId.setsFinite ≠ ClassifierId.ringsDivision := by decide
  simp [evalClassifier, magmasClassifier, setsClassifier, associative, commutative, unital,
    inverse, additive, multiplicative, division]

/-- The Finite classifier is certified on its actual Sets host. -/
theorem specimenFiniteClassifierRealization :
    ClassifierRealization Realization.Mathlib.atomicModel.{0}
      Realization.Mathlib.specimenRingBinding exprSets ClassifierId.setsFinite
      ⟨Normalized.Sets Realization.Mathlib.atomicModel,
        Realization.Mathlib.atomicModel.foundations.finite.total,
        Realization.Mathlib.atomicModel.foundations.finite.forget⟩ := by
  constructor
  have associative : ClassifierId.setsFinite ≠ ClassifierId.magmasAssociative := by decide
  have commutative : ClassifierId.setsFinite ≠ ClassifierId.magmasCommutative := by decide
  have unital : ClassifierId.setsFinite ≠ ClassifierId.magmasUnital := by decide
  have inverse : ClassifierId.setsFinite ≠ ClassifierId.magmasInverse := by decide
  have additive : ClassifierId.setsFinite ≠ ClassifierId.magmasAdditive := by decide
  have multiplicative : ClassifierId.setsFinite ≠ ClassifierId.magmasMultiplicative := by decide
  have division : ClassifierId.setsFinite ≠ ClassifierId.ringsDivision := by decide
  simp [evalClassifier, magmasClassifier, setsClassifier, associative, commutative,
    unital, inverse, additive, multiplicative, division]

example :
    (EvaluatedFunctor.pullbackCategory
      (M := Realization.Mathlib.atomicModel)
      ⟨Normalized.Sets Realization.Mathlib.atomicModel, Normalized.Sets Realization.Mathlib.atomicModel,
        specimenSetsIdentity⟩
      ⟨Normalized.Sets Realization.Mathlib.atomicModel, Normalized.Sets Realization.Mathlib.atomicModel,
        specimenSetsIdentity⟩
      (Normalized.Sets Realization.Mathlib.atomicModel)).isSome = true := by
  simp [EvaluatedFunctor.pullbackCategory]

/-- The binary-operation classifier realizes the registered Magmas node. -/
noncomputable def specimenMagmasRealization :
    CategoryRealization Realization.Mathlib.atomicModel.{0}
      Realization.Mathlib.specimenRingBinding (FunctorSemantics.empty _)
      exprMagmas (Normalized.Magmas Realization.Mathlib.atomicModel) := by
  refine ⟨Normalized.Magmas Realization.Mathlib.atomicModel, ?_, CategoryTheory.Equivalence.refl⟩
  rfl

/-- The evaluator's identity reindex is equivalent to the authored Semigroups category. -/
noncomputable def specimenSemigroupsRealization :
    CategoryRealization Realization.Mathlib.atomicModel.{0}
      Realization.Mathlib.specimenRingBinding (FunctorSemantics.empty _)
      exprSemigroups (Normalized.Semigroups Realization.Mathlib.atomicModel) := by
  let A := Realization.Mathlib.atomicModel.algebra.associative
  refine ⟨(Classifier.reindex (CategoryTheory.CategoryStruct.id _) A).total, ?_, ?_⟩
  · have inverse : ClassifierId.magmasAssociative ≠ ClassifierId.magmasInverse := by decide
    simp [evalCategory, exprSemigroups, Categories.Algebra.Magmas.Semigroups,
      Categories.Algebra.Magmas.Magmas, Categories.Algebra.Magmas.Associative,
      magmasClassifier, forgetfulToMagmas,
      Normalized.Magmas, Realization.Mathlib.atomicModel,
      Realization.Mathlib.atomicModelComponents, A, inverse]
  · exact (ForMathlib.reindexIdIso A).equiv

/-- The Groups expression evaluates through the unital-magma inverse classifier. -/
example :
    (evalCategory Realization.Mathlib.atomicModel.{0} Realization.Mathlib.specimenRingBinding
      (FunctorSemantics.empty _) exprGroups).isSome = true := by
  simp [evalCategory, exprGroups,
    Categories.Algebra.Magmas.Groups, Categories.Algebra.Magmas.Monoids,
    Categories.Algebra.Magmas.Semigroups, Categories.Algebra.Magmas.Magmas,
    Categories.Algebra.Magmas.Associative, Categories.Algebra.Magmas.Unital,
    Categories.Algebra.Magmas.Inverse, magmasClassifier, forgetfulToMagmas,
    forgetfulToUnitalMagma, Realization.Mathlib.atomicModel,
    Realization.Mathlib.atomicModelComponents]

/-- The opaque two-operation host is realized by its declared Mathlib category. -/
noncomputable def specimenMagmasWithTwoOperationsRealization :
    CategoryRealization Realization.Mathlib.atomicModel.{0}
      Realization.Mathlib.specimenRingBinding (FunctorSemantics.empty _)
      exprMagmasWithTwoOperations
      (Normalized.MagmasWithTwoOperations Realization.Mathlib.atomicModel) := by
  refine ⟨Normalized.MagmasWithTwoOperations Realization.Mathlib.atomicModel, ?_,
    CategoryTheory.Equivalence.refl⟩
  rfl

/-- Implicit unnamed target: constructible, not a named registry node. -/
def specimenNamed : NamedExpressionTable where
  bodyOf
    | ⟨"cat.sets"⟩ => some exprSets
    | ⟨"cat.magmas"⟩ => some exprMagmas
    | ⟨"cat.semigroups"⟩ => some exprSemigroups
    | ⟨"cat.monoids"⟩ => some exprMonoids
    | ⟨"cat.groups"⟩ => some exprGroups
    | ⟨"cat.additive_magmas"⟩ => some exprAdditiveMagmas
    | ⟨"cat.additive_semigroups"⟩ => some exprAdditiveSemigroups
    | ⟨"cat.additive_monoids"⟩ => some exprAdditiveMonoids
    | ⟨"cat.additive_groups"⟩ => some exprAdditiveGroups
    | ⟨"cat.rings"⟩ => some exprRings
    | ⟨"cat.commutative_rings"⟩ => some exprCommRings
    | ⟨"cat.division_rings"⟩ => some exprDivisionRings
    | ⟨"cat.modules_r"⟩ => some exprModules
    | ⟨"cat.freemodules"⟩ => some exprFreeModules
    | ⟨"cat.finitelygeneratedmodules"⟩ => some exprFinitelyGeneratedModules
    | ⟨"cat.finiterankmodules"⟩ => some exprFiniteRankModules
    | ⟨"cat.magmaswithtwooperations"⟩ => some exprMagmasWithTwoOperations
    | ⟨"cat.crystals"⟩ => some (.opaque CategoryId.crystals)
    | _ => none

def specimenOpaquePorts : OpaquePortTable where
  port
    | ⟨"cat.magmaswithtwooperations"⟩, ⟨"cat.magmas"⟩, .port ⟨"port.multiplicative"⟩ =>
        some ⟨"oport.m2o.multiplicative"⟩
    | ⟨"cat.magmaswithtwooperations"⟩, ⟨"cat.magmas"⟩, .port ⟨"port.additive"⟩ =>
        some ⟨"oport.m2o.additive"⟩
    | ⟨"cat.magmaswithtwooperations"⟩, ⟨"cat.magmas"⟩, .route ⟨"route.multiplicative"⟩ =>
        some ⟨"oport.m2o.multiplicative"⟩
    | ⟨"cat.magmaswithtwooperations"⟩, ⟨"cat.magmas"⟩, .route ⟨"route.additive"⟩ =>
        some ⟨"oport.m2o.additive"⟩
    | ⟨"cat.modules_r"⟩, ⟨"cat.sets"⟩, _ =>
        some ⟨"oport.modules.sets"⟩
    | ⟨"cat.crystals"⟩, ⟨"cat.sets"⟩, _ =>
        some ⟨"oport.crystals.sets"⟩
    | _, _, _ => none

def specimenFamilyPorts : CategoryFamilyPortTable where
  port
    | family, _, .atom target, _ =>
        if family == CategoryFamilyId.modules && target == CategoryId.sets then
          some ⟨"oport.modules.sets"⟩
        else
          none
    | _, _, _, _ => none

def specimenFamilySignatures : CategoryFamilySignatureTable where
  arity
    | ⟨"fam.modules"⟩ => some 1
    | _ => none

def specimenCtx : ProjectionContext where
  hosts := specimenHosts
  aliases := specimenAliases
  named := specimenNamed
  opaquePorts := specimenOpaquePorts
  familyPorts := specimenFamilyPorts
  familySignatures := specimenFamilySignatures
  refinementId := fun base clf route =>
    let r := match route with
      | some rid => rid.raw
      | none => "default"
    ⟨s!"ref.{toString (repr base)}.{clf.raw}.{r}"⟩

/-! ## Normalization / alias checks (`partial` ⇒ `native_decide`) -/

example :
    specimenAliases.canonicalize ⟨"cat.crings"⟩ = CategoryId.commutativeRings := by
  native_decide

example :
    isIdentityEdge ⟨"cat.crings"⟩ CategoryId.commutativeRings specimenAliases = true := by
  native_decide

example :
    isIdentityEdge CategoryId.commutativeRings CategoryId.commutativeRings specimenAliases =
      true := by
  native_decide

/-! ## Projection checks -/

example :
    (project specimenCtx exprGroups exprMagmas .none).isSome = true := by
  native_decide

example :
    (project specimenCtx exprFiniteRankModules exprSets .none).isSome = true := by
  native_decide

/-- Opaque two-operation host → Magmas along the multiplicative port.
Target is the named atom `cat.magmas` (not the classifier-total body). -/
example :
    (project specimenCtx exprMagmasWithTwoOperations (.atom CategoryId.magmas)
      (.route RouteId.multiplicative)).isSome = true := by
  native_decide

example :
    (project specimenCtx exprRingsGradedFinite (.atom CategoryId.rings) .none).isSome =
      true := by
  native_decide

example :
    Option.isNone (project specimenCtx (.familyApp CategoryFamilyId.modules #[])
      (.atom CategoryId.sets) .none) = true := by
  native_decide

example :
    Option.isNone (project specimenCtx
      (.familyApp CategoryFamilyId.modules #[.ringVariable RingParameterId.r, .ringVariable RingParameterId.r])
      (.atom CategoryId.sets) .none) = true := by
  native_decide

/-! ## Syntactic equality after projection normalization -/

example :
    categoryExprEq specimenCtx (.atom ⟨"cat.crings"⟩)
      (.atom CategoryId.commutativeRings) = true := by
  native_decide

example :
    categoryExprEq specimenCtx
      (.constructor ⟨"ctor.example"⟩ #[exprRings, exprGroups])
      (.constructor ⟨"ctor.example"⟩ #[exprGroups, exprRings]) = false := by
  native_decide

/-- Spelling convenience; registry records aliasOf, not a second category. -/
abbrev CRings := CategoryId.commutativeRings

end CategoryGraph.Specimen

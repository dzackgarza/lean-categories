/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Id
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Lean

@[expose] public section

/-!
# Symbolic category and structural-map expressions

Every declaration has (1) a categorical semantic term and (2) a normalized
symbolic expression. Names are not semantic constructors: they point at
expressions via the registry.
-/

namespace LeanCategories

open CategoryTheory

universe u v

/-- The bounded dependent parameter schemas used by registered families. -/
inductive CategoryFamilySchema
  | ring
  | commRing
  | commRingModule
  | commRingNat
  | commRingIndexType
  | domain
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

/-- Export metadata owned by a family schema. -/
structure CategoryFamilyParameter where
  name : String
  kind : ParameterKindId
  ids : List ParameterId
  dependency : Option Nat := none
  deriving Repr, Inhabited

namespace CategoryFamilySchema

def ringParameterIds : List ParameterId := [ParameterId.r, ParameterId.s]

def moduleParameterIds : List ParameterId := [ParameterId.w, ParameterId.wPrime]

def ringParameter : CategoryFamilyParameter :=
  { name := "R", kind := ParameterKindId.ringObject, ids := ringParameterIds }

def commRingParameter : CategoryFamilyParameter :=
  { name := "R", kind := ParameterKindId.commRingObject, ids := ringParameterIds }

def moduleParameter : CategoryFamilyParameter :=
  { name := "W", kind := ParameterKindId.moduleObject, ids := moduleParameterIds,
    dependency := some 0 }

def natParameter : CategoryFamilyParameter :=
  { name := "n", kind := ParameterKindId.nat, ids := [ParameterId.n] }

def indexTypeParameter : CategoryFamilyParameter :=
  { name := "I", kind := ParameterKindId.indexType, ids := [ParameterId.i] }

def domainParameter : CategoryFamilyParameter :=
  { name := "domain", kind := ParameterKindId.domain, ids := [ParameterId.domain],
    dependency := some 0 }

def parameterMetadata : CategoryFamilySchema → Array CategoryFamilyParameter
  | .ring => #[ringParameter]
  | .commRing => #[commRingParameter]
  | .commRingModule => #[commRingParameter, moduleParameter]
  | .commRingNat => #[commRingParameter, natParameter]
  | .commRingIndexType => #[commRingParameter, indexTypeParameter]
  | .domain => #[commRingParameter, domainParameter]

def dependencyParameterId (schema : CategoryFamilySchema)
    (parameter : CategoryFamilyParameter) : Option ParameterId := do
  let dependency ← parameter.dependency
  let dependencyParameter ← schema.parameterMetadata[dependency]?
  dependencyParameter.ids.head?

@[reducible] def Parameters : CategoryFamilySchema → Type (max (u + 1) (v + 1))
  | .ring => ULift.{v + 1} (RingCat.{u})
  | .commRing => ULift.{v + 1} (Discrete (CommRingCat.{u}))
  | .commRingModule =>
      ULift.{v + 1} (Discrete (Σ R : CommRingCat.{u}, ModuleCat.{u} R))
  | .commRingNat => ULift.{v + 1} (Discrete (Σ _R : CommRingCat.{u}, Nat))
  | .commRingIndexType => Discrete (Σ _R : CommRingCat.{u}, Type v)
  | .domain => ULift.{v + 1} (Discrete (PSigma fun _R : CommRingCat.{u} => IsDomain _R))

/-- Independent-universe carrier for `commRingIndexType` family parameters. -/
def indexTypeParameters : Type (max (u + 1) (v + 1)) :=
  Discrete (Σ _R : CommRingCat.{u}, Type v)

end CategoryFamilySchema

deriving instance Lean.ToExpr for CategoryId
deriving instance Lean.ToExpr for ClassifierId
deriving instance Lean.ToExpr for CategoryFamilyId
deriving instance Lean.ToExpr for ParameterId
deriving instance Lean.ToExpr for ParameterOperationId
deriving instance Lean.ToExpr for ParameterKindId
deriving instance Lean.ToExpr for VarianceId
deriving instance Lean.ToExpr for FunctorId
deriving instance Lean.ToExpr for NaturalTransformationId
deriving instance Lean.ToExpr for PortId
deriving instance Lean.ToExpr for AliasId
deriving instance Lean.ToExpr for OpaquePortId

/-- The semantic kind of a registered family transport. -/
inductive CategoryFamilyTransportSemantics
  | restrictionOfScalars
  | discrete
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

namespace CategoryFamilyTransportSemantics

def variance : CategoryFamilyTransportSemantics → VarianceId
  | .restrictionOfScalars => VarianceId.restrictionOfScalarsContravariant
  | .discrete => VarianceId.discrete

end CategoryFamilyTransportSemantics

/-- Parameter expression for family applications (symbolic). -/
inductive ParameterExpr
  | variable (id : ParameterId)
  | apply (operation : ParameterOperationId) (argument : ParameterExpr)
  | apply2 (operation : ParameterOperationId) (left right : ParameterExpr)
  | apply3 (operation : ParameterOperationId)
      (first second third : ParameterExpr)
  deriving DecidableEq, Repr, Lean.ToExpr

namespace CategoryFamilySchema

inductive ParameterSort
  | ring
  | commRing
  | module (base : ParameterExpr)
  | nat
  | indexType
  | domain (base : ParameterExpr)

def parameterSort (schema : CategoryFamilySchema) (args : Array ParameterExpr) :
    ParameterExpr → Option ParameterSort
  | .variable id =>
      match schema.parameterMetadata.find? (fun parameter => parameter.ids.contains id) with
      | some parameter =>
          if parameter.kind == ParameterKindId.ringObject then some .ring
          else if parameter.kind == ParameterKindId.commRingObject then some .commRing
          else if parameter.kind == ParameterKindId.nat then some .nat
          else if parameter.kind == ParameterKindId.indexType then some .indexType
          else do
            let base ← dependencyParameterId schema parameter
            if parameter.kind == ParameterKindId.domain then
              some (.domain (.variable base))
            else
              some (.module (.variable base))
      | none => none
  | .apply operation argument =>
      if operation == ParameterOperationId.opposite then
        match parameterSort schema args argument with
        | some (.ring) => some .ring
        | some (.commRing) => some .commRing
        | _ => none
      else
        none
  | .apply2 _ _ _ => none
  | .apply3 operation first second third =>
      if schema == .commRingModule && operation == ParameterOperationId.tensorProduct then
        match parameterSort schema args first, parameterSort schema args second,
            parameterSort schema args third with
        | some (.commRing), some (.commRing), some (.module base) =>
            if base == first then some (.module second) else none
        | _, _, _ => none
      else
        none

def parameterSortCompatible : ParameterSort → ParameterSort → Bool
  | .ring, .ring | .commRing, .commRing => true
  | .nat, .nat => true
  | .indexType, .indexType => true
  | .module actual, .module expected => actual == expected
  | .domain actual, .domain expected => actual == expected
  | _, _ => false

def parameterExpectedSort (schema : CategoryFamilySchema) (args : Array ParameterExpr)
    (index : Nat) : Option ParameterSort := do
  let parameter ← schema.parameterMetadata[index]?
  if parameter.kind == ParameterKindId.ringObject then
    some .ring
  else if parameter.kind == ParameterKindId.commRingObject then
    some .commRing
  else if parameter.kind == ParameterKindId.nat then
    some .nat
  else if parameter.kind == ParameterKindId.indexType then
    some .indexType
  else
    let dependency ← parameter.dependency
    let base ← args[dependency]?
    if parameter.kind == ParameterKindId.domain then
      some (.domain base)
    else
      some (.module base)

def parameterSortAt (schema : CategoryFamilySchema) (args : Array ParameterExpr)
    (index : Nat) : Option ParameterSort := do
  let argument ← args[index]?
  match argument with
  | .variable id =>
      let parameter ← schema.parameterMetadata[index]?
      if !parameter.ids.contains id then
        none
      else if parameter.kind == ParameterKindId.moduleObject then
        let dependency ← parameter.dependency
        let base ← args[dependency]?
        some (.module base)
      else if parameter.kind == ParameterKindId.domain then
        let dependency ← parameter.dependency
        let base ← args[dependency]?
        some (.domain base)
      else if parameter.kind == ParameterKindId.ringObject then
        some .ring
      else if parameter.kind == ParameterKindId.nat then
        some .nat
      else if parameter.kind == ParameterKindId.indexType then
        some .indexType
      else
        some .commRing
  | _ => parameterSort schema args argument

def parameterArgsValid (args : Array ParameterExpr) (schema : CategoryFamilySchema) : Bool :=
  args.size == schema.parameterMetadata.size &&
    (List.range args.size).all fun index =>
      (parameterSortAt schema args index).any fun actual =>
        (parameterExpectedSort schema args index).any
          (parameterSortCompatible actual)

end CategoryFamilySchema

/-- Registered symbolic category language. -/
inductive CategoryExpr
  | atom (id : CategoryId)
  | familyApp (family : CategoryFamilyId) (args : Array ParameterExpr)
  | classifierTotal (classifier : ClassifierId)
  | refine (base : CategoryExpr) (classifier : ClassifierId)
  | opaque (id : CategoryId)
  deriving Repr, Lean.ToExpr

/--
Typed symbolic functor language.  Composition is legal only when the middle
category is literally shared by the two legs.
-/
inductive FunctorExpr : CategoryExpr → CategoryExpr → Type
  | identity (category : CategoryExpr) : FunctorExpr category category
  | atomic {source target : CategoryExpr} (id : FunctorId) : FunctorExpr source target
  | classifierForget (classifier : ClassifierId) (host : CategoryExpr) :
      FunctorExpr (.classifierTotal classifier) host
  | opaquePort {source target : CategoryExpr} (port : OpaquePortId) : FunctorExpr source target
  | comp {source middle target : CategoryExpr}
      (left : FunctorExpr source middle) (right : FunctorExpr middle target) :
      FunctorExpr source target
  deriving Repr, Lean.ToExpr

/-!
Typed natural-transformation expressions.

The functor indices enforce parallel endpoints for vertical composition and
the middle-category match for horizontal composition.  These constructors
mirror Mathlib's `NatTrans.id`, `NatTrans.vcomp`, and horizontal composition
(`◫`), without introducing a second semantic category-theory API.
-/
inductive NatTransExpr : {source target : CategoryExpr} →
    FunctorExpr source target → FunctorExpr source target → Type
  | identity {source target : CategoryExpr} (functor : FunctorExpr source target) :
      NatTransExpr functor functor
  | atomic {source target : CategoryExpr}
      {left right : FunctorExpr source target} (id : NaturalTransformationId) :
      NatTransExpr left right
  | vcomp {source target : CategoryExpr}
      {left middle right : FunctorExpr source target}
      (first : NatTransExpr left middle) (second : NatTransExpr middle right) :
      NatTransExpr left right
  | hcomp {source middle target : CategoryExpr}
      {left right : FunctorExpr source middle} {top bottom : FunctorExpr middle target}
      (first : NatTransExpr left right) (second : NatTransExpr top bottom) :
      NatTransExpr (.comp left top) (.comp right bottom)
  deriving Repr, Lean.ToExpr

/-- Syntactic equality of normalized category expressions, independent of rendered syntax. -/
partial def CategoryExpr.syntacticEq : CategoryExpr → CategoryExpr → Bool
  | .atom left, .atom right => left == right
  | .familyApp leftFamily leftArgs, .familyApp rightFamily rightArgs =>
      leftFamily == rightFamily && leftArgs == rightArgs
  | .classifierTotal left, .classifierTotal right => left == right
  | .refine leftBase leftClassifier, .refine rightBase rightClassifier =>
      leftBase.syntacticEq rightBase && leftClassifier == rightClassifier
  | .opaque left, .opaque right => left == right
  | _, _ => false

namespace CategoryExpr

instance : Inhabited CategoryExpr := ⟨.atom ⟨""⟩⟩

/-- Convenience: refine a category by a classifier. -/
def refine' (base : CategoryExpr) (classifier : ClassifierId) : CategoryExpr :=
  .refine base classifier

/-- Convenience: atom. -/
def ofId (id : CategoryId) : CategoryExpr :=
  .atom id

end CategoryExpr

end LeanCategories

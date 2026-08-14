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

universe u

/-- The bounded dependent parameter schemas used by registered families. -/
inductive CategoryFamilySchema
  | ring
  | commRing
  | commRingModule
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

def parameterMetadata : CategoryFamilySchema → Array CategoryFamilyParameter
  | .ring => #[ringParameter]
  | .commRing => #[commRingParameter]
  | .commRingModule => #[commRingParameter, moduleParameter]

def dependencyParameterId (schema : CategoryFamilySchema)
    (parameter : CategoryFamilyParameter) : Option ParameterId := do
  let dependency ← parameter.dependency
  let dependencyParameter ← schema.parameterMetadata[dependency]?
  dependencyParameter.ids.head?

@[reducible] def Parameters : CategoryFamilySchema → Type (u + 1)
  | .ring => RingCat.{u}
  | .commRing => Discrete (CommRingCat.{u})
  | .commRingModule => Discrete (Σ R : CommRingCat.{u}, ModuleCat.{u} R)

end CategoryFamilySchema

deriving instance Lean.ToExpr for CategoryId
deriving instance Lean.ToExpr for ClassifierId
deriving instance Lean.ToExpr for CategoryFamilyId
deriving instance Lean.ToExpr for ParameterId
deriving instance Lean.ToExpr for ParameterOperationId
deriving instance Lean.ToExpr for ParameterKindId
deriving instance Lean.ToExpr for VarianceId
deriving instance Lean.ToExpr for FunctorId
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

def parameterSort (schema : CategoryFamilySchema) (args : Array ParameterExpr) :
    ParameterExpr → Option ParameterSort
  | .variable id =>
      match schema.parameterMetadata.find? (fun parameter => parameter.ids.contains id) with
      | some parameter =>
          if parameter.kind == ParameterKindId.ringObject then some .ring
          else if parameter.kind == ParameterKindId.commRingObject then some .commRing
          else do
            let base ← dependencyParameterId schema parameter
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
  | .module actual, .module expected => actual == expected
  | _, _ => false

def parameterExpectedSort (schema : CategoryFamilySchema) (args : Array ParameterExpr)
    (index : Nat) : Option ParameterSort := do
  let parameter ← schema.parameterMetadata[index]?
  if parameter.kind == ParameterKindId.ringObject then
    some .ring
  else if parameter.kind == ParameterKindId.commRingObject then
    some .commRing
  else
    let dependency ← parameter.dependency
    let base ← args[dependency]?
    some (.module base)

def parameterSortAt (schema : CategoryFamilySchema) (args : Array ParameterExpr)
    (index : Nat) : Option ParameterSort := do
  let argument ← args[index]?
  match argument with
  | .variable id =>
      let parameter ← schema.parameterMetadata.find?
        (fun parameter => parameter.ids.contains id)
      if parameter.kind == ParameterKindId.moduleObject then
        let dependency ← parameter.dependency
        let base ← args[dependency]?
        some (.module base)
      else if parameter.kind == ParameterKindId.ringObject then
        some .ring
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

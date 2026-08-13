/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Id
public import Lean

@[expose] public section

/-!
# Symbolic category and structural-map expressions

Every declaration has (1) a categorical semantic term and (2) a normalized
symbolic expression. Names are not semantic constructors: they point at
expressions via the registry.
-/

namespace LeanCategories

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
  deriving Repr, Inhabited

namespace CategoryFamilySchema

def parameterMetadata : CategoryFamilySchema → Array CategoryFamilyParameter
  | .ring => #[{ name := "R", kind := ParameterKindId.ringObject }]
  | .commRing => #[{ name := "R", kind := ParameterKindId.commRingObject }]
  | .commRingModule => #[{ name := "R", kind := ParameterKindId.commRingObject },
      { name := "W", kind := ParameterKindId.moduleObject }]

end CategoryFamilySchema

deriving instance Lean.ToExpr for CategoryId
deriving instance Lean.ToExpr for ClassifierId
deriving instance Lean.ToExpr for CategoryFamilyId
deriving instance Lean.ToExpr for ParameterId
deriving instance Lean.ToExpr for ParameterOperationId
deriving instance Lean.ToExpr for ParameterKindId
deriving instance Lean.ToExpr for VarianceId
deriving instance Lean.ToExpr for ConstructorId
deriving instance Lean.ToExpr for FunctorId
deriving instance Lean.ToExpr for PortId
deriving instance Lean.ToExpr for AliasId
deriving instance Lean.ToExpr for RouteId
deriving instance Lean.ToExpr for RefinementId
deriving instance Lean.ToExpr for StructuralTheoremId
deriving instance Lean.ToExpr for OpaquePortId
deriving instance Lean.ToExpr for ConeCertificateId
deriving instance Lean.ToExpr for CoherenceId
deriving instance Lean.ToExpr for PresentationId
deriving instance Lean.ToExpr for ClusterId

/-- Parameter expression for family applications (symbolic). -/
inductive ParameterExpr
  | variable (id : ParameterId)
  | apply (operation : ParameterOperationId) (argument : ParameterExpr)
  | apply2 (operation : ParameterOperationId) (left right : ParameterExpr)
  | apply3 (operation : ParameterOperationId)
      (first second third : ParameterExpr)
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Normalized symbolic category language. -/
inductive CategoryExpr
  | atom (id : CategoryId)
  | familyApp (family : CategoryFamilyId) (args : Array ParameterExpr)
  | classifierTotal (classifier : ClassifierId)
  | refine (base : CategoryExpr) (classifier : ClassifierId) (route : Option RouteId)
  /-- Pullback legs are typed functor declarations resolved from the registry. -/
  | pullback (left right : FunctorId) (over : CategoryExpr)
  | constructor (constructor : ConstructorId) (args : Array CategoryExpr)
  | opaque (id : CategoryId)
  | reference (id : CategoryId)
  deriving Repr, Lean.ToExpr

/-- A refinement occurrence with source, base, and classifier-total indices. -/
inductive RefinementExpr : CategoryExpr → CategoryExpr → CategoryExpr → Type
  | mk (id : RefinementId) (base : CategoryExpr) (classifier : ClassifierId)
      (route : Option RouteId) :
      RefinementExpr (.refine base classifier route) base (.classifierTotal classifier)
  deriving Repr, Lean.ToExpr

/--
Typed symbolic functor language.  Composition is legal only when the middle
category is literally shared by the two legs.
-/
inductive FunctorExpr : CategoryExpr → CategoryExpr → Type
  | identity (category : CategoryExpr) : FunctorExpr category category
  | normalizedIdentity (source target : CategoryExpr) : FunctorExpr source target
  /-- A named functor whose endpoints are supplied by the dependent indices. -/
  | atomic {source target : CategoryExpr} (id : FunctorId) : FunctorExpr source target
  | named {source target : CategoryExpr} (id : FunctorId) : FunctorExpr source target
  | baseProjection {refined base total : CategoryExpr}
      (refinement : RefinementExpr refined base total) : FunctorExpr refined base
  | classifierProjection {refined base total : CategoryExpr}
      (refinement : RefinementExpr refined base total) : FunctorExpr refined total
  | classifierForget (classifier : ClassifierId) (host : CategoryId) :
      FunctorExpr (.classifierTotal classifier) (.atom host)
  | unfoldAtom (id : CategoryId) (body : CategoryExpr) :
      FunctorExpr (.atom id) body
  | unfoldReference (id : CategoryId) (body : CategoryExpr) :
      FunctorExpr (.reference id) body
  | opaquePort {source target : CategoryExpr} (port : OpaquePortId) : FunctorExpr source target
  | theoremInclusion {source target : CategoryExpr} (theoremId : StructuralTheoremId) :
      FunctorExpr source target
  | finiteLimitLift {source target : CategoryExpr} (cone : ConeCertificateId) : FunctorExpr source target
  | constructorMap {source target : CategoryExpr} (constructor : ConstructorId) : FunctorExpr source target
  | compose {source middle target : CategoryExpr} (first : FunctorExpr source middle)
      (second : FunctorExpr middle target) : FunctorExpr source target
  deriving Repr, Lean.ToExpr

/-- A typed functor expression with existential source and target indices. -/
structure SomeFunctorExpr where
  source : CategoryExpr
  target : CategoryExpr
  expression : FunctorExpr source target

/-- Syntactic equality of normalized category expressions, independent of rendered syntax. -/
partial def CategoryExpr.syntacticEq : CategoryExpr → CategoryExpr → Bool
  | .atom left, .atom right => left == right
  | .familyApp leftFamily leftArgs, .familyApp rightFamily rightArgs =>
      leftFamily == rightFamily && leftArgs == rightArgs
  | .classifierTotal left, .classifierTotal right => left == right
  | .refine leftBase leftClassifier leftRoute, .refine rightBase rightClassifier rightRoute =>
      leftBase.syntacticEq rightBase && leftClassifier == rightClassifier && leftRoute == rightRoute
  | .pullback leftLeg rightLeg leftOver, .pullback rightLeftLeg rightRightLeg rightOver =>
      leftLeg == rightLeftLeg && rightLeg == rightRightLeg &&
        leftOver.syntacticEq rightOver
  | .constructor leftConstructor leftArgs, .constructor rightConstructor rightArgs =>
      leftConstructor == rightConstructor && leftArgs.size == rightArgs.size &&
        (leftArgs.zipWith (·.syntacticEq ·) rightArgs).all id
  | .opaque left, .opaque right => left == right
  | .reference left, .reference right => left == right
  | _, _ => false

/-- How a named node relates to its expression body. -/
inductive CategoryOrigin
  | root
  | atomicClassifierTotal
  | derivedNamed
  | constructorValue
  | opaqueCategory
  | alias
  deriving DecidableEq, Repr, Inhabited

/-- Visibility for semantic vs presentation layers. -/
inductive Visibility
  /-- Present in semantic export and eligible for presentation. -/
  | present
  /-- Semantic-only (opaque hosts excluded from presentation). -/
  | semanticOnly
  /-- Explicitly excluded from presentation. -/
  | presentationHidden
  deriving DecidableEq, Repr, Inhabited

/-- Route selector for multi-port projection / refine. -/
inductive RouteSelector
  | none
  | port (id : PortId)
  | route (id : RouteId)
  deriving DecidableEq, Repr, Inhabited

namespace CategoryExpr

instance : Inhabited CategoryExpr := ⟨.atom ⟨""⟩⟩

/-- Convenience: refine without a route. -/
def refine' (base : CategoryExpr) (classifier : ClassifierId) : CategoryExpr :=
  .refine base classifier none

/-- Convenience: atom. -/
def ofId (id : CategoryId) : CategoryExpr :=
  .atom id

end CategoryExpr

end LeanCategories

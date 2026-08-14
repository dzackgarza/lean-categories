/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.Entry
public import LeanCategories.CategoryTheory.OneCat.Classifier
public import LeanCategories.Catalogue.Realization
public import Lean
public meta import LeanCategories.Catalogue.Syntax

@[expose] public section

/-!
# Persistent registry extension

`addImportedFn` receives `Array (Array RegistryEntry)` from imported modules.
-/

namespace LeanCategories

open Lean
open Lean Meta
open Lean Elab Command

inductive RegistryEntry
  | category (e : NamedCategoryEntry)
  | categoryFamily (e : CategoryFamilyEntry)
  | classifier (e : ClassifierEntry)
  | functor (e : FunctorEntry)
  | alias (e : AliasEntry)
  | opaque (e : OpaqueCategoryEntry)
  deriving Repr

/-- Stable identifier represented by a heterogeneous registry entry. -/
def RegistryEntry.stableId : RegistryEntry → String
  | .category e => e.id.raw
  | .categoryFamily e => e.id.raw
  | .classifier e => e.id.raw
  | .functor e => e.id.raw
  | .alias e => e.id.raw
  | .opaque e => e.id.raw

/-- Lean declarations that must resolve before this row can be persisted. -/
def RegistryEntry.declarations : RegistryEntry → Array Name
  | .category e => #[e.declaration, e.realization]
  | .categoryFamily e => #[e.realization, e.transport]
  | .classifier e => #[e.declaration, e.realization]
  | .functor e => #[e.declaration, e.realization]
  | .alias e => #[e.declaration, e.realization]
  | .opaque e => #[e.declaration] ++ e.ports.flatMap fun p => #[p.declaration, p.realization]

structure RegistryState where
  categories : Array NamedCategoryEntry := #[]
  categoryFamilies : Array CategoryFamilyEntry := #[]
  classifiers : Array ClassifierEntry := #[]
  functors : Array FunctorEntry := #[]
  aliases : Array AliasEntry := #[]
  opaqueCategories : Array OpaqueCategoryEntry := #[]
  deriving Inhabited

def RegistryState.opaquePortIds (state : RegistryState) : List OpaquePortId :=
  state.opaqueCategories.toList.flatMap fun category => category.ports.toList.map (·.id)

/-- Registered functor lookup by stable ID. -/
def RegistryState.functor? (state : RegistryState) (id : FunctorId) : Option FunctorEntry :=
  state.functors.find? fun entry => entry.id == id

/-- Registered category-family lookup by stable ID. -/
def RegistryState.categoryFamily? (state : RegistryState) (id : CategoryFamilyId) :
    Option CategoryFamilyEntry :=
  state.categoryFamilies.find? fun entry => entry.id == id

def RegistryState.category? (state : RegistryState) (expression : CategoryExpr) :
    Option NamedCategoryEntry :=
  state.categories.find? fun entry => entry.expression.syntacticEq expression

def RegistryState.classifier? (state : RegistryState) (id : ClassifierId) :
    Option ClassifierEntry :=
  state.classifiers.find? fun entry => entry.id == id

/-- Typed opaque-port lookup by stable ID. -/
def RegistryState.opaquePort? (state : RegistryState) (id : OpaquePortId) : Option StructuralPortEntry :=
  state.opaqueCategories.foldl (fun found category =>
    match found with
    | some _ => found
    | none => category.ports.find? fun port => port.id == id) none

def duplicateOpaquePortId : List OpaquePortId → Option OpaquePortId
  | [] => none
  | port :: ports =>
      if ports.any fun other => other == port then some port
      else duplicateOpaquePortId ports

def atomCategoryIdMatchesExpression (id : CategoryId) (expression : CategoryExpr) : Bool :=
  match expression with
  | .atom expressionId => expressionId == id
  | _ => true

/-- Whether two symbolic category endpoints are syntactically identical. -/
def sameEndpoint (left right : CategoryExpr) : Bool :=
  left.syntacticEq right

/-- Whether an expression denotes the stable category ID of an opaque port endpoint. -/
def denotesCategory (expression : CategoryExpr) (endpoint : CategoryExpr) : Bool :=
  expression.syntacticEq endpoint

def refinementDepth : CategoryExpr → Nat
  | .refine parent _ _ => refinementDepth parent + 1
  | _ => 0

def refinementHostInChainFuel (_state : RegistryState) (target : CategoryExpr) :
    Nat → CategoryExpr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      if sameEndpoint target expression then true
      else match expression with
        | .refine parent classifier _ =>
            (_state.classifier? classifier).any fun entry =>
              refinementHostInChainFuel _state entry.host fuel parent &&
                (refinementHostInChainFuel _state target fuel parent ||
                  refinementHostInChainFuel _state target fuel (.classifierTotal classifier))
        | .atom id =>
            match _state.categories.find? (·.id == id) with
            | some entry =>
                if sameEndpoint entry.expression expression then
                  false
                else
                  refinementHostInChainFuel _state target fuel entry.expression
            | none => false
        | .opaque id =>
            _state.opaqueCategories.any fun entry =>
              entry.id == id && entry.ports.any fun port => sameEndpoint port.target target
        | _ => false

/-- A refinement descends from both its parent and its classifier total. -/
def refinementHostInChain (state : RegistryState) (target : CategoryExpr)
    (expression : CategoryExpr) : Bool :=
  refinementHostInChainFuel state target
    (refinementDepth expression + state.categories.size + state.opaqueCategories.size + 1) expression

def ancestryProbeState : RegistryState :=
  { classifiers := #[
      { id := ⟨"clf.first"⟩, canonicalName := "first"
        declaration := ``sameEndpoint, host := .atom ⟨"cat.host"⟩
        realization := ``sameEndpoint, visibility := .present },
      { id := ⟨"clf.second"⟩, canonicalName := "second"
        declaration := ``sameEndpoint, host := .atom ⟨"cat.host"⟩
        realization := ``sameEndpoint, visibility := .present }] }

example : refinementHostInChain ancestryProbeState (.atom ⟨"cat.host"⟩)
    (.refine (.refine (.atom ⟨"cat.host"⟩) ⟨"clf.first"⟩ none) ⟨"clf.second"⟩ none) := by
  native_decide

example : !refinementHostInChain ancestryProbeState (.atom ⟨"cat.host"⟩)
    (.refine (.atom ⟨"cat.other"⟩) ⟨"clf.latest"⟩ none) := by
  native_decide

example : !atomCategoryIdMatchesExpression ⟨"cat.host"⟩ (.atom ⟨"cat.other"⟩) := by
  native_decide

example : duplicateOpaquePortId
    [⟨"port.same"⟩, ⟨"port.same"⟩] = some ⟨"port.same"⟩ := by
  native_decide

partial def CategoryExpr.isRegistered (state : RegistryState) : CategoryExpr → Bool
  | .atom id =>
      state.categories.any (·.id == id) || state.opaqueCategories.any (·.id == id)
  | .familyApp family args =>
      (state.categoryFamily? family).any fun entry =>
        CategoryFamilySchema.parameterArgsValid args entry.schema
  | .classifierTotal classifier => (state.classifier? classifier).isSome
  | .refine base classifier _ =>
      base.isRegistered state &&
        (state.classifier? classifier).isSome
  | .pullback left right over =>
      over.isRegistered state && (state.functor? left).isSome && (state.functor? right).isSome
  | .opaque id => state.categories.any (·.id == id) || state.opaqueCategories.any (·.id == id)
  | .reference _ => false

/- The schema rejects a module whose base is not the selected ring. -/
example : !CategoryFamilySchema.parameterArgsValid #[.variable ParameterId.r]
    .commRingModule := by decide

/- A ring family cannot accept a dependent module parameter. -/
example : !CategoryFamilySchema.parameterArgsValid #[.variable ParameterId.r, .variable ParameterId.w]
    .ring := by decide

/-- Validate references within a typed functor expression against prior persistent entries. -/
partial def FunctorExpr.referencesValid (state : RegistryState)
    {source target : CategoryExpr} : FunctorExpr source target → Bool
  | .identity _ | .normalizedIdentity _ _ => true
  | .atomic _ => true
  | .named id =>
      match state.functor? id with
      | some entry => sameEndpoint entry.source source && sameEndpoint entry.target target
      | none => false
  | .baseProjection _ | .classifierProjection _ | .classifierForget _ _ => true
  | .unfoldAtom _ _ | .unfoldReference _ _ => true
  | .opaquePort id =>
      match state.opaquePort? id with
      | some entry => denotesCategory source entry.source && denotesCategory target entry.target
      | none => false
  | .compose first second => first.referencesValid state && second.referencesValid state

/-- Validate the cospan references of a pullback category before it is persisted. -/
partial def CategoryExpr.referencesValid (state : RegistryState) : CategoryExpr → Bool
  | .atom _ => true
  | .classifierTotal classifier => (state.classifier? classifier).isSome
  | .opaque _ => true
  | .reference _ => false
  | .familyApp family args =>
      match state.categoryFamily? family with
      | some entry => CategoryFamilySchema.parameterArgsValid args entry.schema
      | none => false
  | .refine base classifier _ =>
      base.referencesValid state &&
        (state.classifier? classifier).any fun entry =>
          refinementHostInChain state entry.host base && entry.host.referencesValid state
  | .pullback left right over =>
      match state.functor? left, state.functor? right with
      | some leftEntry, some rightEntry =>
          over.referencesValid state && sameEndpoint leftEntry.target over &&
            sameEndpoint rightEntry.target over
      | _, _ => false

def RegistryState.apply : RegistryState → RegistryEntry → RegistryState
  | s, .category e => { s with categories := s.categories.push e }
  | s, .categoryFamily e => { s with categoryFamilies := s.categoryFamilies.push e }
  | s, .classifier e => { s with classifiers := s.classifiers.push e }
  | s, .functor e => { s with functors := s.functors.push e }
  | s, .alias e => { s with aliases := s.aliases.push e }
  | s, .opaque e => { s with opaqueCategories := s.opaqueCategories.push e }

def duplicateImportedOpaquePortId (as : Array (Array RegistryEntry)) : Option OpaquePortId :=
  duplicateOpaquePortId
    (RegistryState.opaquePortIds (mkStateFromImportedEntries RegistryState.apply {} as))

def importedOpaquePortProbeEntries : Array (Array RegistryEntry) := #[
  #[RegistryEntry.opaque (OpaqueCategoryEntry.mk ⟨"cat.first"⟩ ``sameEndpoint #[
    StructuralPortEntry.mk ⟨"port.imported"⟩ (.atom ⟨"cat.first"⟩)
      (.atom ⟨"cat.first"⟩) ``sameEndpoint ``sameEndpoint "probe" ]
    "probe" .present)],
  #[RegistryEntry.opaque (OpaqueCategoryEntry.mk ⟨"cat.second"⟩ ``sameEndpoint #[
    StructuralPortEntry.mk ⟨"port.imported"⟩ (.atom ⟨"cat.second"⟩)
      (.atom ⟨"cat.second"⟩) ``sameEndpoint ``sameEndpoint "probe" ]
    "probe" .present)] ]

example : duplicateImportedOpaquePortId importedOpaquePortProbeEntries =
    some ⟨"port.imported"⟩ := by
  native_decide

/-- Whether this entry's typed stable ID has already been registered. -/
def RegistryState.hasEntryId : RegistryState → RegistryEntry → Bool
  | state, .category e => state.categories.any (·.id == e.id)
  | state, .categoryFamily e => state.categoryFamilies.any (·.id == e.id)
  | state, .classifier e => state.classifiers.any (·.id == e.id)
  | state, .functor e => state.functors.any (·.id == e.id)
  | state, .alias e => state.aliases.any (·.id == e.id)
  | state, .opaque e => state.opaqueCategories.any (·.id == e.id)

initialize registryExt : SimplePersistentEnvExtension RegistryEntry RegistryState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := RegistryState.apply
    addImportedFn := fun as =>
      let state := mkStateFromImportedEntries RegistryState.apply {} as
      match duplicateOpaquePortId state.opaquePortIds with
      | some id => panic! s!"duplicate opaque port ID {id.raw} in imported registry modules"
      | none => state
  }

def getRegistry (env : Environment) : RegistryState :=
  registryExt.getState env

def addRegistryEntry (e : RegistryEntry) : CoreM Unit := do
  let env ← getEnv
  let state := getRegistry env
  if state.hasEntryId e then
    throwError "duplicate normalized-category registry ID: {e.stableId}"
  match e with
  | .category entry =>
      unless atomCategoryIdMatchesExpression entry.id entry.expression do
        throwError "category atom {entry.id.raw} does not use its own category expression"
      let isSelf := match entry.expression with
        | .atom id | .opaque id => id == entry.id
        | _ => false
      if (!entry.expression.isRegistered state && !isSelf) ||
          !entry.expression.referencesValid state then
        throwError "category entry {entry.id.raw} has an unresolved or ill-typed functor reference"
  | .functor entry =>
      if !entry.source.isRegistered state || !entry.target.isRegistered state ||
          !entry.source.referencesValid state || !entry.target.referencesValid state ||
          !entry.expression.referencesValid state then
        throwError "functor entry {entry.id.raw} has an unresolved or unregistered endpoint"
  | .classifier entry =>
      unless entry.host.isRegistered state && entry.host.referencesValid state do
        throwError "classifier entry {entry.id.raw} has an unresolved or unregistered host"
  | .alias entry =>
      unless state.categories.any (·.id == entry.aliasOf) do
        throwError "alias entry {entry.id.raw} refers to an unregistered category"
  | .opaque entry =>
      unless state.categories.any (·.id == entry.id) do
        throwError "opaque category entry {entry.id.raw} has no registered category"
      for port in entry.ports do
        unless port.source.isRegistered state && port.target.isRegistered state do
          throwError "opaque port {port.id.raw} has an unregistered endpoint"
      match duplicateOpaquePortId (entry.ports.toList.map (·.id)) with
      | some id => throwError "duplicate opaque port ID {id.raw}"
      | none => pure ()
      for category in state.opaqueCategories do
        for port in entry.ports do
          unless !category.ports.any fun registered => registered.id == port.id do
            throwError "duplicate opaque port ID {port.id.raw}"
  | _ => pure ()
  for declaration in e.declarations do
    if declaration.isAnonymous then
      throwError "registry entry {e.stableId} has no declaration name"
    if (env.find? declaration).isNone then
      throwError "registry entry {e.stableId} refers to unknown declaration {declaration}"
  modifyEnv (registryExt.addEntry · e)

/-- The result type of a declaration after exposing all of its parameters. -/
def declarationResultType (declaration : Name) : MetaM Expr := do
  let info ← getConstInfo declaration
  forallTelescopeReducing info.type fun _ result => pure result

/-- Require a declaration to return an actual category object. -/
def ensureCategoryDeclaration (declaration : Name) : MetaM Unit := do
  let result ← declarationResultType declaration
  unless result.isConstOf ``LeanCategories.ObjCat do
    throwError "registry declaration {declaration} must return ObjCat, but returns {result}"

/-- Require a category-realization declaration to have the typed witness form. -/
def ensureCategoryRealization (realization : Name) : MetaM Unit := do
  let result ← declarationResultType realization
  unless result.isAppOf ``LeanCategories.CategoryRealization do
    throwError
      "registry realization {realization} must return CategoryRealization ..., but returns {result}"

def validateRegisteredCategoryEndpointRealization (state : RegistryState) (expression : CategoryExpr)
    (category realization : Expr) : MetaM Unit := do
  let realizationType ← withTransparency .all <| whnf (← inferType realization)
  unless realizationType.isAppOf ``LeanCategories.CategoryRealization do
    throwError "category endpoint realization is not a CategoryRealization"
  let realizationArgs := realizationType.getAppArgs
  unless realizationArgs.size == 2 do
    throwError "category endpoint realization has malformed parameters"
  unless ← withTransparency .all <| isDefEq (Lean.toExpr expression) realizationArgs[0]! do
    throwError "category endpoint realization has the wrong expression"
  unless ← withTransparency .all <| isDefEq category realizationArgs[1]! do
    throwError "category endpoint realization has the wrong category"
  let familyFibre ← withTransparency .all do
    mkAppM ``LeanCategories.CategoryRealization.familyFibre #[realization]
  let familyFibre ← withTransparency .all <| whnf familyFibre
  match expression with
  | .familyApp family familyArgs =>
      let familyEntry ← match state.categoryFamily? family with
        | some entry => pure entry
        | none => throwError "family endpoint has no registered family"
      unless CategoryFamilySchema.parameterArgsValid familyArgs familyEntry.schema do
        throwError "family endpoint has invalid parameter quotations"
      unless familyFibre.isAppOf ``Option.some do
        throwError "family endpoint realization has no typed fibre witness"
      let packed := familyFibre.getAppArgs.back!
      let witness := packed.getAppArgs.back!
      let witnessType ← withTransparency .all <| inferType witness
      let witnessTypeArgs := witnessType.getAppArgs
      unless witnessTypeArgs.size >= 4 do
        throwError "family endpoint realization has a malformed fibre witness"
      let witnessIdentifier := witnessTypeArgs[1]!
      let witnessRealization := witnessTypeArgs[3]!
      let familyValue ← mkAppM ``LeanCategories.CategoryFamilyId.mk #[mkStrLit family.raw]
      unless ← withTransparency .all <| isDefEq witnessIdentifier familyValue do
        throwError "family endpoint realization has the wrong family witness"
      let registeredRealization ← mkConstWithFreshMVarLevels familyEntry.realization
      unless ← withTransparency .all <| isDefEq witnessRealization registeredRealization do
        throwError "family endpoint realization is not the exact registered family realization"
      let witnessArguments ← withTransparency .all do
        mkAppM ``LeanCategories.CategoryFamilyFibreWitness.arguments #[witness]
      unless ← withTransparency .all <| isDefEq (Lean.toExpr familyArgs) witnessArguments do
        throwError "family endpoint realization has unrelated symbolic arguments"
      let categoryEq ← withTransparency .all do
        mkAppM ``LeanCategories.CategoryFamilyFibreWitness.category_eq #[witness]
      let categoryEqType ← withTransparency .all <| inferType categoryEq
      unless categoryEqType.isEq do
        throwError "family endpoint realization has no category equality witness"
      unless ← withTransparency .all <| isDefEq categoryEqType.getAppArgs[1]! category do
        throwError "family endpoint realization has the wrong category witness"
  | _ =>
      let entry ← match state.category? expression with
        | some entry => pure entry
        | none => throwError "category endpoint has no registered category realization"
      let registeredRealization ← mkConstWithFreshMVarLevels entry.realization
      let registeredType ← inferType registeredRealization
      let (parameters, _, _) ← forallMetaTelescopeReducing registeredType
      let registeredValue := mkAppN registeredRealization parameters
      unless ← withTransparency .all <| isDefEq realization registeredValue do
        throwError
          "category endpoint realization is not the exact registered realization {entry.realization}"
      unless familyFibre.isAppOfArity ``Option.none 1 do
        throwError "non-family endpoint realization has a family fibre witness"

def validateClassifierTotalEndpointRealization (state : RegistryState)
    (classifier : ClassifierId) (category realization : Expr) : MetaM Unit := do
  let classifierEntry ← match state.classifier? classifier with
    | some entry => pure entry
    | none => throwError "classifier endpoint {classifier.raw} has no registered classifier"
  let realizationType ← withTransparency .all <| whnf (← inferType realization)
  unless realizationType.isAppOf ``LeanCategories.CategoryRealization do
    throwError "classifier total realization is not a CategoryRealization"
  let realizationArgs := realizationType.getAppArgs
  unless realizationArgs.size == 2 do
    throwError "classifier total realization has malformed parameters"
  let expression : CategoryExpr := .classifierTotal classifier
  unless ← withTransparency .all <| isDefEq (Lean.toExpr expression) realizationArgs[0]! do
    throwError "classifier total realization has the wrong expression"
  unless ← withTransparency .all <| isDefEq category realizationArgs[1]! do
    throwError "classifier total realization has the wrong category"
  let registeredConstant ← mkConstWithFreshMVarLevels classifierEntry.realization
  let registeredType ← inferType registeredConstant
  let (parameters, _, _) ← forallMetaTelescopeReducing registeredType
  let registeredValue := mkAppN registeredConstant parameters
  let registeredTotal ← withTransparency .all do
    mkAppM ``LeanCategories.ClassifierRealization.totalRealization #[registeredValue]
  unless ← withTransparency .all <| isDefEq realization registeredTotal do
    throwError "classifier total realization is not the exact registered classifier realization"
  let familyFibre ← withTransparency .all do
    mkAppM ``LeanCategories.CategoryRealization.familyFibre #[realization]
  let familyFibre ← withTransparency .all <| whnf familyFibre
  unless familyFibre.isAppOfArity ``Option.none 1 do
    throwError "non-family classifier total realization has a family fibre witness"

def validateRefinementEndpointRealization (state : RegistryState)
    (base : CategoryExpr) (classifier : ClassifierId) : MetaM Unit := do
  let classifierEntry ← match state.classifier? classifier with
    | some entry => pure entry
    | none => throwError "refinement classifier {classifier.raw} has no registered classifier"
  unless refinementHostInChain state classifierEntry.host base do
    throwError "refinement classifier {classifier.raw} has no registered host ancestry"

def validateCategoryEndpointRealization (state : RegistryState) (expression : CategoryExpr)
    (category realization : Expr) : MetaM Unit :=
  match expression with
  | .classifierTotal classifier =>
      validateClassifierTotalEndpointRealization state classifier category realization
  | _ => validateRegisteredCategoryEndpointRealization state expression category realization

def validateAliasDeclarationRealization (state : RegistryState) (entry : AliasEntry) : MetaM Unit := do
  let target ← match state.categories.find? (fun category => category.id == entry.aliasOf) with
    | some target => pure target
    | none => throwError "alias entry {entry.id.raw} has no registered target category"
  let targetValue ← mkConstWithFreshMVarLevels target.declaration
  let targetType ← inferType targetValue
  let (targetParameters, _, _) ← forallMetaTelescopeReducing targetType
  let targetValue := mkAppN targetValue targetParameters
  let aliasValue ← mkConstWithFreshMVarLevels entry.declaration
  unless ← withTransparency .all <| isDefEq aliasValue targetValue do
    throwError "alias entry {entry.id.raw} declaration is not its target category"
  let aliasRealization ← mkConstWithFreshMVarLevels entry.realization
  validateRegisteredCategoryEndpointRealization state target.expression targetValue aliasRealization

def validateOpaquePortRealization (state : RegistryState) (entry : StructuralPortEntry) : MetaM Unit := do
  let realizationConstant ← mkConstWithFreshMVarLevels entry.realization
  let realizationType ← inferType realizationConstant
  forallTelescopeReducing realizationType fun arguments realizationResult => do
    let realizationValue := mkAppN realizationConstant arguments
    let realizationArgs := realizationResult.getAppArgs
    unless realizationArgs.size == 6 do
      throwError "opaque port realization {entry.realization} has malformed parameters"
    let expression : FunctorExpr entry.source entry.target := .opaquePort entry.id
    unless ← withTransparency .all <| isDefEq (Lean.toExpr entry.source) realizationArgs[0]! do
      throwError "opaque port realization {entry.realization} has the wrong source"
    unless ← withTransparency .all <| isDefEq (Lean.toExpr entry.target) realizationArgs[1]! do
      throwError "opaque port realization {entry.realization} has the wrong target"
    unless ← withTransparency .all <| isDefEq (Lean.toExpr expression) realizationArgs[2]! do
      throwError "opaque port realization {entry.realization} has the wrong expression"
    let declarationValue ← mkConstWithFreshMVarLevels entry.declaration
    let declarationValue := mkAppN declarationValue arguments
    unless ← withTransparency .all <| isDefEq declarationValue realizationArgs[5]! do
      throwError "opaque port declaration {entry.declaration} is not its realization"
    let sourceRealization ← withTransparency .all do
      mkAppM ``LeanCategories.FunctorRealization.sourceRealization #[realizationValue]
    let targetRealization ← withTransparency .all do
      mkAppM ``LeanCategories.FunctorRealization.targetRealization #[realizationValue]
    let sourceType ← withTransparency .all <| whnf (← inferType sourceRealization)
    let targetType ← withTransparency .all <| whnf (← inferType targetRealization)
    let sourceArgs := sourceType.getAppArgs
    let targetArgs := targetType.getAppArgs
    unless sourceArgs.size == 2 && targetArgs.size == 2 do
      throwError "opaque port endpoint realization has malformed parameters"
    validateCategoryEndpointRealization state entry.source sourceArgs[1]! sourceRealization
    validateCategoryEndpointRealization state entry.target targetArgs[1]! targetRealization

def validateCategoryDeclarationRealization (state : RegistryState) (expression : CategoryExpr)
    (declaration realization : Name) (familyRealization : Option Name) : MetaM Unit := do
  let realizationConstant ← mkConstWithFreshMVarLevels realization
  let realizationValue := realizationConstant
  let realizationType ← inferType realizationValue
  forallTelescopeReducing realizationType fun arguments realizationResult => do
    let realizationArgs := realizationResult.getAppArgs
    unless realizationArgs.size == 2 do
      throwError "registry realization {realization} has malformed CategoryRealization parameters"
    unless ← withTransparency .all <| isDefEq (Lean.toExpr expression) realizationArgs[0]! do
      throwError
        "registry category expression does not match realization {realization}"
    let declarationValue ← mkConstWithFreshMVarLevels declaration
    let declarationValue := mkAppN declarationValue arguments
    unless ← isDefEq declarationValue realizationArgs[1]! do
      throwError
        "registry category declaration {declaration} does not match realization {realization}"
    let realizationValue := mkAppN realizationConstant arguments
    match expression with
    | .classifierTotal classifier =>
        validateClassifierTotalEndpointRealization state classifier realizationArgs[1]!
          realizationValue
    | .refine base classifier _ =>
        validateRefinementEndpointRealization state base classifier
    | _ => pure ()
    let familyFibre ← withTransparency .all do
      mkAppM ``LeanCategories.CategoryRealization.familyFibre #[mkAppN realizationConstant arguments]
    let familyFibre ← withTransparency .all <| whnf familyFibre
    match expression, familyRealization with
    | .familyApp family familyArgs, some familyRealization => do
        let realizationValue := mkAppN realizationConstant arguments
        let witnessOption ← withTransparency .all do
          let witnessOption ←
            mkAppM ``LeanCategories.CategoryRealization.familyFibre #[realizationValue]
          whnf witnessOption
        unless witnessOption.isAppOf ``Option.some do
          throwError
            "registry family category {declaration} lacks a typed fibre witness"
        let packedArgs := witnessOption.getAppArgs
        let packed := packedArgs.back!
        let packedFields := packed.getAppArgs
        unless packedFields.size >= 2 do
          throwError "registry family category {declaration} has malformed fibre witness"
        let witness := packedFields.back!
        let witnessType ← withTransparency .all <| inferType witness
        let witnessTypeArgs := witnessType.getAppArgs
        unless witnessTypeArgs.size >= 4 do
          throwError "registry family category {declaration} has malformed realization type"
        let witnessIdentifier := witnessTypeArgs[1]!
        let witnessRealization := witnessTypeArgs[3]!
        let familyValue ← mkAppM ``LeanCategories.CategoryFamilyId.mk #[mkStrLit family.raw]
        unless ← withTransparency .all <| isDefEq witnessIdentifier familyValue do
          throwError "registry family category {declaration} has the wrong family witness"
        let familyConstant ← mkConstWithFreshMVarLevels familyRealization
        let registeredRealization := mkAppN familyConstant #[]
        unless ← withTransparency .all <| isDefEq witnessRealization registeredRealization do
          throwError "registry family category {declaration} has a non-registered family realization"
        let witnessArguments ← withTransparency .all do
          mkAppM ``LeanCategories.CategoryFamilyFibreWitness.arguments #[witness]
        unless ← withTransparency .all <| isDefEq (Lean.toExpr familyArgs) witnessArguments do
          throwError "registry family category {declaration} has symbolic arguments unrelated to its fibre parameter"
        let categoryEq ← withTransparency .all do
          mkAppM ``LeanCategories.CategoryFamilyFibreWitness.category_eq #[witness]
        let categoryEqType ← withTransparency .all <| inferType categoryEq
        unless categoryEqType.isEq do
          throwError "registry family category {declaration} has no category equality witness"
        unless ← withTransparency .all <| isDefEq categoryEqType.getAppArgs[1]! realizationArgs[1]! do
          throwError "registry family category {declaration} witness has the wrong category"
        let familyValue := witnessRealization
        let parameter ← withTransparency .all do
          mkAppM ``LeanCategories.CategoryFamilyFibreWitness.parameter #[witness]
        let fibre ← withTransparency .all do
          mkAppM ``LeanCategories.CategoryFamilyRealization.fibre #[familyValue, parameter]
        unless ← withTransparency .all <| isDefEq categoryEqType.getAppArgs[2]! fibre do
          throwError "registry family category {declaration} is not its selected family fibre"
    | .familyApp _ _, none =>
        throwError "registry family category {declaration} has no registered family realization"
    | _, some _ =>
        throwError "non-family category {declaration} carries a family fibre witness"
    | _, none =>
        unless familyFibre.isAppOfArity ``Option.none 1 do
          throwError "non-family category {declaration} has a non-empty family fibre witness"

/-- Require a functor-realization declaration to have the typed witness form. -/
def ensureFunctorRealization (realization : Name) : MetaM Unit := do
  let result ← declarationResultType realization
  unless result.isAppOf ``LeanCategories.FunctorRealization do
    throwError
      "registry realization {realization} must return FunctorRealization ..., but returns {result}"

def FunctorExpr.classifierForget? {source target : CategoryExpr}
    : FunctorExpr source target → Option (ClassifierId × CategoryExpr)
  | .classifierForget classifier host => some (classifier, host)
  | _ => none

def validateFunctorDeclarationRealization (_state : RegistryState) {source target : CategoryExpr}
    (expression : FunctorExpr source target)
    (declaration realization : Name) : MetaM Unit := do
  let realizationConstant ← mkConstWithFreshMVarLevels realization
  let realizationType ← inferType realizationConstant
  forallTelescopeReducing realizationType fun arguments realizationResult => do
    let realizationValue := mkAppN realizationConstant arguments
    let realizationArgs := realizationResult.getAppArgs
    unless realizationArgs.size == 6 do
      throwError "registry realization {realization} has malformed FunctorRealization parameters"
    let expressionValue := Lean.toExpr expression
    let expressionType ← inferType expressionValue
    let expressionTypeArgs := expressionType.getAppArgs
    unless expressionTypeArgs.size == 2 do
      throwError "registry functor expression has malformed endpoints"
    unless ← withTransparency .all <| isDefEq expressionTypeArgs[0]! realizationArgs[0]! do
      throwError "registry functor source does not match realization {realization}"
    unless ← withTransparency .all <| isDefEq expressionTypeArgs[1]! realizationArgs[1]! do
      throwError "registry functor target does not match realization {realization}"
    unless ← withTransparency .all <| isDefEq expressionValue realizationArgs[2]! do
      throwError "registry functor expression does not match realization {realization}"
    let declarationValue ← mkConstWithFreshMVarLevels declaration
    let declarationValue := mkAppN declarationValue arguments
    let declarationType ← whnf (← inferType declarationValue)
    unless ← withTransparency .all <| isDefEq declarationValue realizationArgs[5]! do
      throwError
          "registry functor declaration {declaration} is not the realized functor {realization}"
    let sourceRealization ← withTransparency .all do
      mkAppM ``LeanCategories.FunctorRealization.sourceRealization #[realizationValue]
    let targetRealization ← withTransparency .all do
      mkAppM ``LeanCategories.FunctorRealization.targetRealization #[realizationValue]
    let sourceType ← withTransparency .all <| whnf (← inferType sourceRealization)
    let targetType ← withTransparency .all <| whnf (← inferType targetRealization)
    let sourceArgs := sourceType.getAppArgs
    let targetArgs := targetType.getAppArgs
    unless sourceArgs.size == 2 && targetArgs.size == 2 do
      throwError "registry functor endpoint realization has malformed parameters"
    match expression.classifierForget? with
    | some (classifier, host) => do
        let classifierEntry ← match _state.classifier? classifier with
          | some entry => pure entry
          | none => throwError "classifier forget {classifier.raw} has no registered classifier"
        unless host.syntacticEq classifierEntry.host do
          throwError "classifier forget {classifier.raw} has the wrong symbolic host"
        let classifierConstant ← mkConstWithFreshMVarLevels classifierEntry.realization
        let classifierType ← inferType classifierConstant
        let (parameters, _, _) ← forallMetaTelescopeReducing classifierType
        let classifierValue := mkAppN classifierConstant parameters
        let registeredHostRealization ← withTransparency .all do
          mkAppM ``LeanCategories.ClassifierRealization.hostRealization #[classifierValue]
        unless ← withTransparency .all <| isDefEq targetRealization registeredHostRealization do
          throwError
            "classifier forget {classifier.raw} is not the exact registered host realization"
    | none => pure ()
    validateCategoryEndpointRealization _state source sourceArgs[1]! sourceRealization
    validateCategoryEndpointRealization _state target targetArgs[1]! targetRealization
    let realizationFunctorType ← whnf (← inferType realizationArgs[5]!)
    let declarationArgs := declarationType.getAppArgs
    let realizationArgs' := realizationFunctorType.getAppArgs
    unless declarationArgs.size >= 2 && realizationArgs'.size >= 2 do
      throwError "registry functor declaration {declaration} has malformed endpoints"
    if declarationType.isAppOfArity ``CategoryTheory.Functor 4 then
      let source ← mkAppM ``CategoryTheory.Cat.of #[declarationArgs[0]!]
      let target ← mkAppM ``CategoryTheory.Cat.of #[declarationArgs[1]!]
      unless ← isDefEq source realizationArgs'[0]! do
        throwError
          "registry functor declaration {declaration} source does not match realization {realization}"
      unless ← isDefEq target realizationArgs'[1]! do
        throwError
          "registry functor declaration {declaration} target does not match realization {realization}"
    else
      unless ← isDefEq declarationArgs[0]! realizationArgs'[0]! do
        throwError
          "registry functor declaration {declaration} source does not match realization {realization}"
      unless ← isDefEq declarationArgs[1]! realizationArgs'[1]! do
        throwError
          "registry functor declaration {declaration} target does not match realization {realization}"

/-- Require a declaration to return a typed family realization. -/
def ensureCategoryFamilyRealization (identifier : CategoryFamilyId) (schema : CategoryFamilySchema)
    (realization : Name) : MetaM Unit := do
  let result ← declarationResultType realization
  unless result.isAppOf ``LeanCategories.CategoryFamilyRealization do
    throwError
      "registry realization {realization} must return CategoryFamilyRealization ..., but returns {result}"
  let arguments := result.getAppArgs
  unless arguments.size == 2 do
    throwError "registry realization {realization} has malformed schema parameters"
  let registeredIdentifier := Lean.toExpr identifier
  unless ← withTransparency .all <| isDefEq registeredIdentifier arguments[0]! do
    throwError "registry realization {realization} does not use the registered family identifier"
  unless ← withTransparency .all <| isDefEq (Lean.toExpr schema) arguments[1]! do
    throwError "registry realization {realization} does not use the registered family schema"

/-- Validate a family transport against the typed realization. -/
def validateCategoryFamilyTransportDecl (_identifier : CategoryFamilyId)
    (schema : CategoryFamilySchema)
    (realization transport : Name) (semantics : CategoryFamilyTransportSemantics) :
    MetaM Unit := do
  let realizationValue ← mkConstWithFreshMVarLevels realization
  let transportValue ← mkConstWithFreshMVarLevels transport
  let realizationTransport ←
    mkAppM ``LeanCategories.CategoryFamilyRealization.transport #[realizationValue]
  let realizationTransportType ← inferType realizationTransport
  let transportType ← inferType transportValue
  unless ← isDefEq realizationTransportType transportType do
    throwError
      "registry family transport {transport} does not have the realization's exact pseudofunctor type"
  unless ← isDefEq realizationTransport transportValue do
    throwError
      "registry family transport {transport} is not the transport used by realization {realization}"
  let realizationSemantics ←
    mkAppM ``LeanCategories.CategoryFamilyRealization.transportSemantics #[realizationValue]
  unless ← isDefEq (Lean.toExpr semantics) realizationSemantics do
    throwError "registry family transport semantics do not match its typed realization"
  match semantics, schema with
  | .restrictionOfScalars, .ring =>
      let mathlibTransport ← mkConstWithFreshMVarLevels
        ``RingCat.moduleCatRestrictScalarsPseudofunctor
      unless ← isDefEq transportValue mathlibTransport do
        throwError "registry restriction-of-scalars transport is not Mathlib's pseudofunctor"
  | .restrictionOfScalars, _ =>
      throwError "restriction-of-scalars semantics require a RingCat family"
  | .discrete, .ring =>
      throwError "RingCat families cannot register equality-only transport semantics"
  | .discrete, .commRing => do
      let canonicalTransport ← withTransparency .all do
        mkAppM ``LeanCategories.CategoryFamilyRealization.canonicalDiscreteCommRingTransport
          #[realizationValue]
      unless ← withTransparency .all <| isDefEq transportValue canonicalTransport do
        throwError
          "registry equality-only transport is not the canonical discrete family transport"
  | .discrete, .commRingModule => do
      let canonicalTransport ← withTransparency .all do
        mkAppM
          ``LeanCategories.CategoryFamilyRealization.canonicalDiscreteCommRingModuleTransport
          #[realizationValue]
      unless ← withTransparency .all <| isDefEq transportValue canonicalTransport do
        throwError
          "registry equality-only transport is not the canonical discrete family transport"

/-- Require a declaration to return a typed classifier realization. -/
def ensureClassifierRealization (realization : Name) : MetaM Unit := do
  let result ← declarationResultType realization
  unless result.isAppOf ``LeanCategories.ClassifierRealization do
    throwError
      "registry realization {realization} must return ClassifierRealization ..., but returns {result}"

/-- Require a declaration to return a classifier after its parameters are supplied. -/
def ensureClassifierDeclaration (declaration : Name) : MetaM Unit := do
  let result ← declarationResultType declaration
  unless result.isAppOfArity ``LeanCategories.Classifier 1 do
    throwError "registry declaration {declaration} must return Classifier _, but returns {result}"

def validateClassifierDeclarationRealization (_state : RegistryState) (entry : ClassifierEntry) :
    MetaM Unit := do
  let realizationConstant ← mkConstWithFreshMVarLevels entry.realization
  let realizationType ← inferType realizationConstant
  forallTelescopeReducing realizationType fun arguments realizationResult => do
    let realizationValue := mkAppN realizationConstant arguments
    let realizationArgs := realizationResult.getAppArgs
    unless realizationArgs.size == 4 do
      throwError "classifier realization {entry.realization} has malformed parameters"
    unless ← withTransparency .all <| isDefEq (Lean.toExpr entry.host) realizationArgs[0]! do
      throwError "classifier realization {entry.realization} has the wrong host"
    unless ← withTransparency .all <| isDefEq (Lean.toExpr entry.id) realizationArgs[1]! do
      throwError "classifier realization {entry.realization} has the wrong identifier"
    let declarationConstant ← mkConstWithFreshMVarLevels entry.declaration
    let declarationValue := mkAppN declarationConstant arguments
    unless ← withTransparency .all <| isDefEq declarationValue realizationArgs[3]! do
      throwError "classifier declaration {entry.declaration} is not the realized classifier"
    let hostRealization ← withTransparency .all do
      mkAppM ``LeanCategories.ClassifierRealization.hostRealization #[realizationValue]
    let totalRealization ← withTransparency .all do
      mkAppM ``LeanCategories.ClassifierRealization.totalRealization #[realizationValue]
    let classifierTotal ← withTransparency .all do
      mkAppM ``LeanCategories.Classifier.total #[declarationValue]
    let hostType ← withTransparency .all <| whnf (← inferType hostRealization)
    let hostArgs := hostType.getAppArgs
    unless hostArgs.size == 2 do
      throwError "classifier host realization has malformed parameters"
    let totalType ← withTransparency .all <| whnf (← inferType totalRealization)
    let totalArgs := totalType.getAppArgs
    unless totalArgs.size == 2 do
      throwError "classifier total realization has malformed parameters"
    validateCategoryEndpointRealization _state entry.host hostArgs[1]! hostRealization
    let stateWithClassifier := _state.apply (.classifier entry)
    validateClassifierTotalEndpointRealization stateWithClassifier entry.id totalArgs[1]!
      totalRealization
    unless ← withTransparency .all <| isDefEq classifierTotal totalArgs[1]! do
      throwError "classifier total realization is not the registered classifier total"

/-- Require a declaration to elaborate to an actual functor between categories. -/
def ensureFunctorDeclaration (declaration : Name) : MetaM Unit := do
  let result ← whnf (← declarationResultType declaration)
  unless result.isAppOfArity ``CategoryTheory.Functor 4 ||
      result.isAppOfArity ``CategoryTheory.Cat.Hom 2 do
    throwError
      "registry declaration {declaration} must return a categorical functor, but returns {result}"

/-- Inspect declaration types before atomically persisting a registry entry. -/
def validateRegistryEntryDeclaration (entry : RegistryEntry) : MetaM Unit := do
  let state := getRegistry (← getEnv)
  match entry with
  | .category e => do
      ensureCategoryDeclaration e.declaration
      ensureCategoryRealization e.realization
      match e.expression with
      | .familyApp family _ =>
          match state.categoryFamily? family with
          | some familyEntry =>
              validateCategoryDeclarationRealization state e.expression e.declaration e.realization
                (some familyEntry.realization)
          | none => throwError "category entry {e.id.raw} refers to an unregistered family"
      | _ => validateCategoryDeclarationRealization state e.expression e.declaration e.realization none
  | .categoryFamily e => do
      ensureCategoryFamilyRealization e.id e.schema e.realization
      validateCategoryFamilyTransportDecl e.id e.schema e.realization e.transport
        e.transportSemantics
  | .classifier e => do
      ensureClassifierDeclaration e.declaration
      ensureClassifierRealization e.realization
      validateClassifierDeclarationRealization state e
  | .functor e => do
      match e.expression with
      | .atomic id =>
          unless id == e.id do
            throwError
              "registry functor {e.id.raw} has an atomic expression for {id.raw}"
      | _ => pure ()
      ensureFunctorDeclaration e.declaration
      ensureFunctorRealization e.realization
      validateFunctorDeclarationRealization state e.expression e.declaration e.realization
  | .alias e => do
      ensureCategoryDeclaration e.declaration
      ensureCategoryRealization e.realization
      validateAliasDeclarationRealization state e
  | .opaque e => do
      ensureCategoryDeclaration e.declaration
      for port in e.ports do
        ensureFunctorDeclaration port.declaration
        ensureFunctorRealization port.realization
        validateOpaquePortRealization state port

/-- Validate the elaborated declaration and persist exactly one registry entry. -/
def addRegistryEntryChecked (entry : RegistryEntry) : MetaM Unit := do
  validateRegistryEntryDeclaration entry
  addRegistryEntry entry

/--
Atomically elaborate and register one authored registry declaration.

The command is deliberately entry-by-entry: an imported module contributes its own
declarations directly to the persistent environment extension instead of assembling a
second in-memory manifest and replaying it later.
-/
syntax (name := normalizedRegistryEntry) "normalized_registry " term : command

elab_rules : command
  | `(normalized_registry $entry) => do
      let command ← `(run_cmd
        liftTermElabM do
          addRegistryEntryChecked $entry)
      elabCommand command

/-- Materialize the registered state for a Lean-authored export. -/
def RegistryState.snapshot (state : RegistryState) (schemaVersion : String) : RegistrySnapshot where
  schemaVersion
  categories := state.categories
  categoryFamilies := state.categoryFamilies
  classifiers := state.classifiers
  functors := state.functors
  aliases := state.aliases
  opaqueCategories := state.opaqueCategories

end LeanCategories

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.Entry
public import LeanCategories.CategoryTheory.OneCat.Classifier
public import LeanCategories.Catalogue.Realization
public import Lean

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
  | constructor (e : ConstructorEntry)
  | finiteLimitCone (e : FiniteLimitConeEntry)
  | coherence (e : CoherenceEntry)
  | theoremInclusion (e : TheoremInclusionEntry)
  | alias (e : AliasEntry)
  | opaque (e : OpaqueCategoryEntry)
  | presentation (e : PresentationMetadataEntry)
  deriving Repr

/-- Stable identifier represented by a heterogeneous registry entry. -/
def RegistryEntry.stableId : RegistryEntry → String
  | .category e => e.id.raw
  | .categoryFamily e => e.id.raw
  | .classifier e => e.id.raw
  | .functor e => e.id.raw
  | .constructor e => e.id.raw
  | .finiteLimitCone e => e.id.raw
  | .coherence e => e.id.raw
  | .theoremInclusion e => e.id.raw
  | .alias e => e.id.raw
  | .opaque e => e.id.raw
  | .presentation e => e.id.raw

/-- Lean declarations that must resolve before this row can be persisted. -/
def RegistryEntry.declarations : RegistryEntry → Array Name
  | .category e => #[e.declaration, e.realization]
  | .categoryFamily e => #[e.realization, e.transport]
  | .classifier e => #[e.declaration, e.realization]
  | .functor e => #[e.declaration, e.realization]
  | .constructor e => #[e.declaration]
  | .finiteLimitCone e => #[e.declaration]
  | .coherence e => #[e.declaration]
  | .theoremInclusion e => #[e.declaration]
  | .alias e => #[e.declaration]
  | .opaque e => #[e.declaration] ++ e.ports.map (·.declaration)
  | .presentation e => #[e.declaration]

structure RegistryState where
  categories : Array NamedCategoryEntry := #[]
  categoryFamilies : Array CategoryFamilyEntry := #[]
  classifiers : Array ClassifierEntry := #[]
  functors : Array FunctorEntry := #[]
  constructors : Array ConstructorEntry := #[]
  finiteLimitCones : Array FiniteLimitConeEntry := #[]
  coherences : Array CoherenceEntry := #[]
  theoremInclusions : Array TheoremInclusionEntry := #[]
  aliases : Array AliasEntry := #[]
  opaqueCategories : Array OpaqueCategoryEntry := #[]
  presentations : Array PresentationMetadataEntry := #[]
  deriving Inhabited

/-- Registered functor lookup by stable ID. -/
def RegistryState.functor? (state : RegistryState) (id : FunctorId) : Option FunctorEntry :=
  state.functors.find? fun entry => entry.id == id

/-- Registered category-family lookup by stable ID. -/
def RegistryState.categoryFamily? (state : RegistryState) (id : CategoryFamilyId) :
    Option CategoryFamilyEntry :=
  state.categoryFamilies.find? fun entry => entry.id == id

/-- Typed opaque-port lookup by stable ID. -/
def RegistryState.opaquePort? (state : RegistryState) (id : OpaquePortId) : Option StructuralPortEntry :=
  state.opaqueCategories.foldl (fun found category =>
    match found with
    | some _ => found
    | none => category.ports.find? fun port => port.id == id) none

/-- Theorem-backed inclusion lookup by stable ID. -/
def RegistryState.theoremInclusion? (state : RegistryState) (id : StructuralTheoremId) :
    Option TheoremInclusionEntry :=
  state.theoremInclusions.find? fun entry => entry.id == id

/-- Finite-limit cone lookup by stable ID. -/
def RegistryState.finiteLimitCone? (state : RegistryState) (id : ConeCertificateId) :
    Option FiniteLimitConeEntry :=
  state.finiteLimitCones.find? fun entry => entry.id == id

/-- Constructor lookup by stable ID. -/
def RegistryState.constructor? (state : RegistryState) (id : ConstructorId) : Option ConstructorEntry :=
  state.constructors.find? fun entry => entry.id == id

/-- Whether two symbolic category endpoints are syntactically identical. -/
def sameEndpoint (left right : CategoryExpr) : Bool :=
  left.syntacticEq right

/-- Whether an expression denotes the stable category ID of an opaque port endpoint. -/
def denotesCategory (expression : CategoryExpr) (id : CategoryId) : Bool :=
  match expression with
  | .atom value | .opaque value | .reference value => value == id
  | _ => false

def ringKind (kind : ParameterKindId) : Bool :=
  kind == ParameterKindId.ringObject || kind == ParameterKindId.commRingObject

def parameterKindOf : ParameterExpr → Option ParameterKindId
  | .variable id =>
      if id == ParameterId.r || id == ParameterId.s then
        some ParameterKindId.ringObject
      else if id == ParameterId.w || id == ParameterId.wPrime then
        some ParameterKindId.moduleObject
      else
        none
  | .apply operation argument =>
      if operation == ParameterOperationId.opposite then
        match parameterKindOf argument with
        | some kind => if ringKind kind then some kind else none
        | none => none
      else
        none
  | .apply2 _ _ _ => none
  | .apply3 operation first second third =>
      if operation == ParameterOperationId.tensorProduct then
        if (parameterKindOf first).any ringKind && (parameterKindOf second).any ringKind then
          if parameterKindOf third == some ParameterKindId.moduleObject then
            some ParameterKindId.moduleObject
          else
            none
        else
          none
      else
        none

def parameterExprReferencesValid : ParameterExpr → Bool
  | .variable id => id == ParameterId.r || id == ParameterId.s ||
      id == ParameterId.w || id == ParameterId.wPrime
  | .apply operation argument =>
      operation == ParameterOperationId.opposite && parameterExprReferencesValid argument
  | .apply2 _ _ _ => false
  | .apply3 operation first second third =>
        operation == ParameterOperationId.tensorProduct && parameterExprReferencesValid first &&
        parameterExprReferencesValid second && parameterExprReferencesValid third

def parameterKindCompatible (actual expected : ParameterKindId) : Bool :=
  actual == expected || actual == ParameterKindId.ringObject &&
    expected == ParameterKindId.commRingObject

def parameterArgsValid (args : Array ParameterExpr)
    (parameters : Array CategoryFamilyParameter) : Bool :=
  if args.size != parameters.size then
    false
  else
    (List.range args.size).all fun index =>
      match args[index]?, parameters[index]? with
      | some argument, some parameter => parameterExprReferencesValid argument &&
          match parameterKindOf argument with
          | some kind => parameterKindCompatible kind parameter.kind
          | none => false
      | _, _ => false

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
  | .theoremInclusion id =>
      match state.theoremInclusion? id with
      | some entry => sameEndpoint entry.source source && sameEndpoint entry.target target
      | none => false
  | .finiteLimitLift id =>
      match state.finiteLimitCone? id with
      | some entry => sameEndpoint entry.source source && sameEndpoint entry.target target
      | none => false
  | .constructorMap id =>
      match state.constructor? id with
      | some entry => sameEndpoint entry.source source && sameEndpoint entry.target target
      | none => false
  | .compose first second => first.referencesValid state && second.referencesValid state

/-- Validate the cospan references of a pullback category before it is persisted. -/
partial def CategoryExpr.referencesValid (state : RegistryState) : CategoryExpr → Bool
  | .atom _ | .classifierTotal _ | .opaque _ | .reference _ => true
  | .familyApp family args =>
      match state.categoryFamily? family with
      | some entry => parameterArgsValid args entry.parameters
      | none => false
  | .refine base _ _ => base.referencesValid state
  | .constructor _ args => (args.map (·.referencesValid state)).all id
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
  | s, .constructor e => { s with constructors := s.constructors.push e }
  | s, .finiteLimitCone e => { s with finiteLimitCones := s.finiteLimitCones.push e }
  | s, .coherence e => { s with coherences := s.coherences.push e }
  | s, .theoremInclusion e => { s with theoremInclusions := s.theoremInclusions.push e }
  | s, .alias e => { s with aliases := s.aliases.push e }
  | s, .opaque e => { s with opaqueCategories := s.opaqueCategories.push e }
  | s, .presentation e => { s with presentations := s.presentations.push e }

/-- Whether this entry's typed stable ID has already been registered. -/
def RegistryState.hasEntryId : RegistryState → RegistryEntry → Bool
  | state, .category e => state.categories.any (·.id == e.id)
  | state, .categoryFamily e => state.categoryFamilies.any (·.id == e.id)
  | state, .classifier e => state.classifiers.any (·.id == e.id)
  | state, .functor e => state.functors.any (·.id == e.id)
  | state, .constructor e => state.constructors.any (·.id == e.id)
  | state, .finiteLimitCone e => state.finiteLimitCones.any (·.id == e.id)
  | state, .coherence e => state.coherences.any (·.id == e.id)
  | state, .theoremInclusion e => state.theoremInclusions.any (·.id == e.id)
  | state, .alias e => state.aliases.any (·.id == e.id)
  | state, .opaque e => state.opaqueCategories.any (·.id == e.id)
  | state, .presentation e => state.presentations.any (·.id == e.id)

initialize registryExt : SimplePersistentEnvExtension RegistryEntry RegistryState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := RegistryState.apply
    addImportedFn := fun as =>
      mkStateFromImportedEntries RegistryState.apply {} as
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
      if !entry.expression.referencesValid state then
        throwError "category entry {entry.id.raw} has an unresolved or ill-typed functor reference"
  | .functor entry =>
      if !entry.source.referencesValid state || !entry.target.referencesValid state ||
          !entry.expression.referencesValid state then
        throwError "functor entry {entry.id.raw} has an unresolved or ill-typed functor reference"
  | .constructor entry =>
      if !entry.source.referencesValid state || !entry.target.referencesValid state then
        throwError "constructor entry {entry.id.raw} has an unresolved category endpoint"
  | .finiteLimitCone entry =>
      if !entry.source.referencesValid state || !entry.target.referencesValid state ||
          !entry.apex.referencesValid state then
        throwError "finite-limit cone entry {entry.id.raw} has an unresolved category endpoint"
  | .theoremInclusion entry =>
      if !entry.source.referencesValid state || !entry.target.referencesValid state then
        throwError "theorem inclusion entry {entry.id.raw} has an unresolved category endpoint"
  | .coherence entry =>
      if (state.functor? entry.source).isNone || (state.functor? entry.target).isNone then
        throwError "coherence entry {entry.id.raw} refers to an unregistered functor"
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

def validateCategoryDeclarationRealization (expression : CategoryExpr)
    (_declaration realization : Name) : MetaM Unit := do
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
    let declarationValue ← mkConstWithFreshMVarLevels _declaration
    let declarationValue := mkAppN declarationValue arguments
    unless ← isDefEq declarationValue realizationArgs[1]! do
      throwError
        "registry category declaration {_declaration} does not match realization {realization}"
    match expression with
    | .familyApp family _ => do
        let realizationValue := mkAppN realizationConstant arguments
        let witnessOption ← withTransparency .all do
          let witnessOption ←
            mkAppM ``LeanCategories.CategoryRealization.familyFibre #[realizationValue]
          whnf witnessOption
        unless witnessOption.isAppOf ``Option.some do
          throwError
            "registry family category {_declaration} lacks a typed fibre witness"
        let witness := witnessOption.getAppArgs.back!
        let witnessIdentifier ← withTransparency .all do
          mkAppM ``LeanCategories.CategoryFamilyFibreWitness.identifier #[witness]
        let familyValue ← mkAppM ``LeanCategories.CategoryFamilyId.mk #[mkStrLit family.raw]
        unless ← withTransparency .all <| isDefEq witnessIdentifier familyValue do
          throwError "registry family category {_declaration} has the wrong family witness"
        let categoryEq ← withTransparency .all do
          mkAppM ``LeanCategories.CategoryFamilyFibreWitness.category_eq #[witness]
        let categoryEqType ← withTransparency .all <| inferType categoryEq
        unless categoryEqType.isEq do
          throwError "registry family category {_declaration} has no category equality witness"
        unless ← withTransparency .all <| isDefEq categoryEqType.getAppArgs[1]! realizationArgs[1]! do
          throwError "registry family category {_declaration} witness has the wrong category"
        let familyValue ← withTransparency .all do
          mkAppM ``LeanCategories.CategoryFamilyFibreWitness.realization #[witness]
        let parameter ← withTransparency .all do
          mkAppM ``LeanCategories.CategoryFamilyFibreWitness.parameter #[witness]
        let fibre ← withTransparency .all do
          mkAppM ``LeanCategories.CategoryFamilyRealization.fibre #[familyValue, parameter]
        unless ← withTransparency .all <| isDefEq categoryEqType.getAppArgs[2]! fibre do
          throwError "registry family category {_declaration} is not its selected family fibre"
    | _ => pure ()

/-- Require a functor-realization declaration to have the typed witness form. -/
def ensureFunctorRealization (realization : Name) : MetaM Unit := do
  let result ← declarationResultType realization
  unless result.isAppOf ``LeanCategories.FunctorRealization do
    throwError
      "registry realization {realization} must return FunctorRealization ..., but returns {result}"

def validateFunctorDeclarationRealization {source target : CategoryExpr}
    (expression : FunctorExpr source target)
    (declaration realization : Name) : MetaM Unit := do
  let realizationValue ← mkConstWithFreshMVarLevels realization
  let realizationType ← inferType realizationValue
  forallTelescopeReducing realizationType fun arguments realizationResult => do
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
def ensureCategoryFamilyRealization (realization : Name) : MetaM Unit := do
  let result ← declarationResultType realization
  unless result.isAppOf ``LeanCategories.CategoryFamilyRealization do
    throwError
      "registry realization {realization} must return CategoryFamilyRealization ..., but returns {result}"

/-- Validate a family transport against the typed realization. -/
def validateCategoryFamilyTransportDecl (realization transport : Name) :
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

/-- Require a declaration to elaborate to an actual functor between categories. -/
def ensureFunctorDeclaration (declaration : Name) : MetaM Unit := do
  let result ← whnf (← declarationResultType declaration)
  unless result.isAppOfArity ``CategoryTheory.Functor 4 ||
      result.isAppOfArity ``CategoryTheory.Cat.Hom 2 do
    throwError
      "registry declaration {declaration} must return a categorical functor, but returns {result}"

/-- Inspect declaration types before atomically persisting a registry entry. -/
def validateRegistryEntryDeclaration (entry : RegistryEntry) : MetaM Unit := do
  match entry with
  | .category e => do
      ensureCategoryDeclaration e.declaration
      ensureCategoryRealization e.realization
      validateCategoryDeclarationRealization e.expression e.declaration e.realization
  | .categoryFamily e => do
      ensureCategoryFamilyRealization e.realization
      validateCategoryFamilyTransportDecl e.realization e.transport
  | .classifier e => do
      ensureClassifierDeclaration e.declaration
      ensureClassifierRealization e.realization
  | .functor e => do
      match e.expression with
      | .atomic id =>
          unless id == e.id do
            throwError
              "registry functor {e.id.raw} has an atomic expression for {id.raw}"
      | _ => pure ()
      ensureFunctorDeclaration e.declaration
      ensureFunctorRealization e.realization
      validateFunctorDeclarationRealization e.expression e.declaration e.realization
  | .constructor e => ensureFunctorDeclaration e.declaration
  | .finiteLimitCone _ => pure ()
  | .coherence _ => pure ()
  | .theoremInclusion e => ensureFunctorDeclaration e.declaration
  | .alias _ => pure ()
  | .opaque e => do
      ensureCategoryDeclaration e.declaration
      for port in e.ports do
        ensureFunctorDeclaration port.declaration
  | .presentation _ => pure ()

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
  constructors := state.constructors
  finiteLimitCones := state.finiteLimitCones
  coherences := state.coherences
  theoremInclusions := state.theoremInclusions
  aliases := state.aliases
  opaqueCategories := state.opaqueCategories
  equivalences := #[]
  presentations := state.presentations

end LeanCategories

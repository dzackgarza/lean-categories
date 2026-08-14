/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.Entry
public import LeanCategories.CategoryTheory.OneCat.Classifier
public import LeanCategories.Catalogue.Realization
public import Lean.Data.Json
public import Lean
public meta import LeanCategories.Catalogue.Syntax

@[expose] public section

set_option backward.privateInPublic true

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
  | .category e => #[e.declaration, e.realization] ++ match e.refinementRealization with
      | some realization => #[realization]
      | none => #[]
  | .categoryFamily e => #[e.realization, e.transport]
  | .classifier e => #[e.declaration, e.realization]
  | .functor e => #[e.declaration, e.realization]
  | .alias e => #[e.declaration, e.realization]
  | .opaque e => #[e.declaration, e.realization] ++
      e.ports.flatMap fun p => #[p.declaration, p.realization]

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
  let candidates := state.categories.filter fun entry => entry.expression.syntacticEq expression;
  (if candidates.size == 1 then candidates[0]? else none)

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

def duplicateOpaqueCategoryId : List CategoryId → Option CategoryId
  | [] => none
  | category :: categories =>
      if categories.any fun other => other == category then some category
      else duplicateOpaqueCategoryId categories

def duplicateCategoryExpressionList : List NamedCategoryEntry → Option CategoryExpr
  | [] => none
  | category :: categories =>
      if categories.any fun other => other.expression.syntacticEq category.expression then
        some category.expression
      else duplicateCategoryExpressionList categories

def duplicateCanonicalNameList : List String → Option String
  | [] => none
  | name :: names =>
      if names.any (· == name) then some name
      else duplicateCanonicalNameList names

def RegistryState.publicLookupSpellings (state : RegistryState) : List String :=
  state.categories.toList.map (·.canonicalName) ++
    state.categoryFamilies.toList.map (·.canonicalName) ++
    state.classifiers.toList.map (·.canonicalName) ++
    state.functors.toList.map (·.canonicalName) ++
    state.aliases.toList.map (·.spelling)

def RegistryState.duplicatePublicLookupSpelling (state : RegistryState) : Option String :=
  duplicateCanonicalNameList state.publicLookupSpellings

def RegistryEntry.publicLookupSpelling : RegistryEntry → Option String
  | .category e => some e.canonicalName
  | .categoryFamily e => some e.canonicalName
  | .classifier e => some e.canonicalName
  | .functor e => some e.canonicalName
  | .alias e => some e.spelling
  | .opaque _ => none

def opaqueCategoryMatchesCategory (category : NamedCategoryEntry)
    (opaqueEntry : OpaqueCategoryEntry) : Bool :=
  category.id == opaqueEntry.id && category.declaration == opaqueEntry.declaration &&
    category.realization == opaqueEntry.realization &&
    category.expression.syntacticEq (.opaque category.id)

def categoryIdMatchesExpression (id : CategoryId) (expression : CategoryExpr) : Bool :=
  match expression with
  | .atom expressionId | .opaque expressionId => expressionId == id
  | _ => true

/-- Whether two symbolic category endpoints are syntactically identical. -/
def sameEndpoint (left right : CategoryExpr) : Bool :=
  left.syntacticEq right

def RegistryState.duplicateCategoryExpression (state : RegistryState) : Option CategoryExpr :=
  duplicateCategoryExpressionList state.categories.toList

private def duplicateCategoryExpressionProbeState : RegistryState :=
  { categories := #[
      { id := ⟨"probe.expression.first"⟩, canonicalName := "probe.expression.first",
        declaration := ``sameEndpoint, expression := .atom ⟨"probe.expression"⟩,
        realization := ``sameEndpoint },
      { id := ⟨"probe.expression.second"⟩, canonicalName := "probe.expression.second",
        declaration := ``sameEndpoint, expression := .atom ⟨"probe.expression"⟩,
        realization := ``sameEndpoint }] }

example : duplicateCategoryExpressionProbeState.duplicateCategoryExpression.isSome := by
  native_decide

example : duplicateCategoryExpressionProbeState.category? (.atom ⟨"probe.expression"⟩) = none := by
  native_decide

private def duplicateCategoryCanonicalNameProbeState : RegistryState :=
  { categories := #[{
      id := ⟨"probe.canonical.category"⟩, canonicalName := "probe.same-name",
      declaration := ``sameEndpoint, expression := .atom ⟨"probe.canonical.category"⟩,
      realization := ``sameEndpoint }]
    categoryFamilies := #[{
      id := ⟨"probe.canonical.family"⟩, canonicalName := "probe.same-name", schema := .ring,
      realization := ``sameEndpoint, transport := ``sameEndpoint,
      transportSemantics := .restrictionOfScalars }] }

example : duplicateCategoryCanonicalNameProbeState.duplicatePublicLookupSpelling =
    some "probe.same-name" := by
  native_decide

/-- Whether an expression denotes the stable category ID of an opaque port endpoint. -/
def denotesCategory (expression : CategoryExpr) (endpoint : CategoryExpr) : Bool :=
  expression.syntacticEq endpoint

def refinementDepth : CategoryExpr → Nat
  | .refine parent _ => refinementDepth parent + 1
  | _ => 0

def refinementHostInChainFuel (_state : RegistryState) (target : CategoryExpr) :
    Nat → CategoryExpr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      if sameEndpoint target expression then true
      else match expression with
        | .refine parent classifier =>
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

private def ancestryProbeState : RegistryState :=
  { classifiers := #[
      { id := ⟨"clf.first"⟩, canonicalName := "first"
        declaration := ``sameEndpoint, host := .atom ⟨"cat.host"⟩
        realization := ``sameEndpoint,},
      { id := ⟨"clf.second"⟩, canonicalName := "second"
        declaration := ``sameEndpoint, host := .atom ⟨"cat.host"⟩
        realization := ``sameEndpoint,}] }

example : refinementHostInChain ancestryProbeState (.atom ⟨"cat.host"⟩)
    (.refine (.refine (.atom ⟨"cat.host"⟩) ⟨"clf.first"⟩) ⟨"clf.second"⟩) := by
  native_decide

example : !refinementHostInChain ancestryProbeState (.atom ⟨"cat.host"⟩)
    (.refine (.atom ⟨"cat.other"⟩) ⟨"clf.latest"⟩) := by
  native_decide

example : !categoryIdMatchesExpression ⟨"cat.host"⟩ (.atom ⟨"cat.other"⟩) := by
  native_decide

example : !categoryIdMatchesExpression ⟨"cat.named"⟩ (.opaque ⟨"cat.other"⟩) := by
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
  | .refine base classifier =>
      base.isRegistered state &&
        (state.classifier? classifier).isSome
  | .opaque id => state.categories.any (·.id == id) || state.opaqueCategories.any (·.id == id)

/- The schema rejects a module whose base is not the selected ring. -/
example : !CategoryFamilySchema.parameterArgsValid #[.variable ParameterId.r]
    .commRingModule := by decide

/- A ring family cannot accept a dependent module parameter. -/
example : !CategoryFamilySchema.parameterArgsValid #[.variable ParameterId.r, .variable ParameterId.w]
    .ring := by decide

/-- Validate references within a typed functor expression against prior persistent entries. -/
partial def FunctorExpr.referencesValid (state : RegistryState)
    {source target : CategoryExpr} : FunctorExpr source target → Bool
  | .identity _ => true
  | .atomic _ => true
  | .classifierForget classifier host =>
      (state.classifier? classifier).any fun entry => sameEndpoint entry.host host
  | .opaquePort id =>
      match state.opaquePort? id with
      | some entry => denotesCategory source entry.source && denotesCategory target entry.target
      | none => false

/-- Validate the cospan references of a pullback category before it is persisted. -/
partial def CategoryExpr.referencesValid (state : RegistryState) : CategoryExpr → Bool
  | .atom _ => true
  | .classifierTotal classifier => (state.classifier? classifier).isSome
  | .opaque _ => true
  | .familyApp family args =>
      match state.categoryFamily? family with
      | some entry => CategoryFamilySchema.parameterArgsValid args entry.schema
      | none => false
  | .refine base classifier =>
      base.referencesValid state &&
        (state.classifier? classifier).any fun entry =>
          refinementHostInChain state entry.host base && entry.host.referencesValid state

private def RegistryState.apply : RegistryState → RegistryEntry → RegistryState
  | s, .category e => { s with categories := s.categories.push e }
  | s, .categoryFamily e => { s with categoryFamilies := s.categoryFamilies.push e }
  | s, .classifier e => { s with classifiers := s.classifiers.push e }
  | s, .functor e => { s with functors := s.functors.push e }
  | s, .alias e => { s with aliases := s.aliases.push e }
  | s, .opaque e => { s with opaqueCategories := s.opaqueCategories.push e }

def RegistryState.registryEntries (state : RegistryState) : List RegistryEntry :=
  state.categories.toList.map RegistryEntry.category ++
    state.categoryFamilies.toList.map RegistryEntry.categoryFamily ++
    state.classifiers.toList.map RegistryEntry.classifier ++
    state.functors.toList.map RegistryEntry.functor ++
    state.aliases.toList.map RegistryEntry.alias ++
    state.opaqueCategories.toList.map RegistryEntry.opaque

def registryEntryPairAllowed : RegistryEntry → RegistryEntry → Bool
  | .category category, right =>
      match right with
      | .opaque opaqueEntry => opaqueCategoryMatchesCategory category opaqueEntry
      | _ => false
  | .opaque opaqueEntry, right =>
      match right with
      | .category category => opaqueCategoryMatchesCategory category opaqueEntry
      | _ => false
  | _, _ => false

def duplicateRegistryEntryId : List RegistryEntry → Option String
  | [] => none
  | entry :: entries =>
      if entries.any fun other =>
          other.stableId == entry.stableId && !registryEntryPairAllowed entry other then
        some entry.stableId
      else duplicateRegistryEntryId entries

def RegistryState.duplicateEntryId (state : RegistryState) : Option String :=
  duplicateRegistryEntryId state.registryEntries

/-- Whether this entry's stable ID conflicts with a retained registry entry. -/
def RegistryState.hasEntryId : RegistryState → RegistryEntry → Bool
  | state, entry => state.registryEntries.any fun existing =>
      existing.stableId == entry.stableId && !registryEntryPairAllowed existing entry

private def duplicateImportedOpaquePortId (as : Array (Array RegistryEntry)) : Option OpaquePortId :=
  duplicateOpaquePortId
    (RegistryState.opaquePortIds (mkStateFromImportedEntries RegistryState.apply {} as))

private def duplicateImportedOpaqueCategoryId (as : Array (Array RegistryEntry)) : Option CategoryId :=
  duplicateOpaqueCategoryId
    ((mkStateFromImportedEntries RegistryState.apply {} as).opaqueCategories.toList.map (·.id))

private def importedOpaquePortProbeEntries : Array (Array RegistryEntry) := #[
  #[RegistryEntry.opaque {
    id := ⟨"cat.first"⟩, declaration := ``sameEndpoint, realization := ``sameEndpoint,
    ports := #[StructuralPortEntry.mk ⟨"port.imported"⟩ (.atom ⟨"cat.first"⟩)
      (.atom ⟨"cat.first"⟩) ``sameEndpoint ``sameEndpoint "probe"],
    reason := "probe",}],
  #[RegistryEntry.opaque {
    id := ⟨"cat.second"⟩, declaration := ``sameEndpoint, realization := ``sameEndpoint,
    ports := #[StructuralPortEntry.mk ⟨"port.imported"⟩ (.atom ⟨"cat.second"⟩)
      (.atom ⟨"cat.second"⟩) ``sameEndpoint ``sameEndpoint "probe"],
    reason := "probe",}] ]

example : duplicateImportedOpaquePortId importedOpaquePortProbeEntries =
    some ⟨"port.imported"⟩ := by
  native_decide

private def duplicateImportedStableIdProbeEntries : Array (Array RegistryEntry) := #[
  #[RegistryEntry.category {
    id := ⟨"probe.duplicate"⟩, canonicalName := "probe.duplicate",
    declaration := ``sameEndpoint, expression := .atom ⟨"probe.duplicate"⟩,
    realization := ``sameEndpoint,}],
  #[RegistryEntry.classifier {
    id := ⟨"probe.duplicate"⟩, canonicalName := "probe.duplicate",
    declaration := ``sameEndpoint, host := .atom ⟨"probe.duplicate"⟩,
    realization := ``sameEndpoint,}]]

example : RegistryState.duplicateEntryId
    (mkStateFromImportedEntries RegistryState.apply {} duplicateImportedStableIdProbeEntries) =
    some "probe.duplicate" := by
  native_decide

private def allRegistryKindsDuplicateProbeState : RegistryState :=
  { categories := #[{
      id := ⟨"probe.all-kinds"⟩, canonicalName := "probe.all-kinds",
      declaration := ``sameEndpoint, expression := .atom ⟨"probe.all-kinds"⟩,
      realization := ``sameEndpoint,}]
    categoryFamilies := #[{
      id := ⟨"probe.all-kinds"⟩, canonicalName := "probe.all-kinds", schema := .ring,
      realization := ``sameEndpoint, transport := ``sameEndpoint,
      transportSemantics := .restrictionOfScalars }]
    classifiers := #[{
      id := ⟨"probe.all-kinds"⟩, canonicalName := "probe.all-kinds",
      declaration := ``sameEndpoint, host := .atom ⟨"probe.all-kinds"⟩,
      realization := ``sameEndpoint,}]
    functors := #[{
      id := ⟨"probe.all-kinds"⟩, canonicalName := "probe.all-kinds",
      source := .atom ⟨"probe.all-kinds"⟩, target := .atom ⟨"probe.all-kinds"⟩,
      declaration := ``sameEndpoint, realization := ``sameEndpoint,
      expression := .atomic ⟨"probe.all-kinds"⟩ }]
    aliases := #[{
      id := ⟨"probe.all-kinds"⟩, spelling := "probe.all-kinds", aliasOf := ⟨"probe.all-kinds"⟩,
      declaration := ``sameEndpoint, realization := ``sameEndpoint }]
    opaqueCategories := #[{
      id := ⟨"probe.all-kinds"⟩, declaration := ``sameEndpoint,
      realization := ``sameEndpoint, ports := #[], reason := "probe",}] }

example : allRegistryKindsDuplicateProbeState.duplicateEntryId = some "probe.all-kinds" := by
  decide

private def localCrossKindDuplicateProbeState : RegistryState :=
  { categories := #[{
      id := ⟨"probe.local-duplicate"⟩, canonicalName := "probe.local-duplicate",
      declaration := ``sameEndpoint, expression := .atom ⟨"probe.local-duplicate"⟩,
      realization := ``sameEndpoint,}] }

private def localCrossKindDuplicateProbeEntry : RegistryEntry := .classifier {
  id := ⟨"probe.local-duplicate"⟩, canonicalName := "probe.local-duplicate",
  declaration := ``sameEndpoint, host := .atom ⟨"probe.local-duplicate"⟩,
  realization := ``sameEndpoint,}

example : localCrossKindDuplicateProbeState.hasEntryId localCrossKindDuplicateProbeEntry := by
  native_decide

private def localNamedOpaqueCompanionProbeState : RegistryState :=
  { categories := #[{
      id := ⟨"probe.local-companion"⟩, canonicalName := "probe.local-companion",
      declaration := ``sameEndpoint, expression := .opaque ⟨"probe.local-companion"⟩,
      realization := ``sameEndpoint,}] }

private def localNamedOpaqueCompanionProbeEntry : RegistryEntry := .opaque {
  id := ⟨"probe.local-companion"⟩, declaration := ``sameEndpoint,
  realization := ``sameEndpoint, ports := #[], reason := "probe",}

example : !localNamedOpaqueCompanionProbeState.hasEntryId
    localNamedOpaqueCompanionProbeEntry := by
  native_decide

private def duplicatePublicLookupSpellingProbeState : RegistryState :=
  { classifiers := #[{
      id := ⟨"probe.lookup.classifier"⟩, canonicalName := "probe.same-spelling",
      declaration := ``sameEndpoint, host := .atom ⟨"probe.lookup.host"⟩,
      realization := ``sameEndpoint }]
    aliases := #[{
      id := ⟨"probe.lookup.alias"⟩, spelling := "probe.same-spelling",
      aliasOf := ⟨"probe.lookup.host"⟩, declaration := ``sameEndpoint,
      realization := ``sameEndpoint }] }

example : duplicatePublicLookupSpellingProbeState.duplicatePublicLookupSpelling =
    some "probe.same-spelling" := by
  decide

example : !opaqueCategoryMatchesCategory
    { id := ⟨"cat.fake.opaque"⟩, canonicalName := "cat.fake.opaque",
      declaration := ``sameEndpoint, expression := .opaque ⟨"existing"⟩,
      realization := ``sameEndpoint,}
    { id := ⟨"cat.fake.opaque"⟩, declaration := ``sameEndpoint,
      realization := ``sameEndpoint, ports := #[], reason := "probe",} := by
  have differentIds : !((.opaque ⟨"existing"⟩ : CategoryExpr).syntacticEq
      (.opaque ⟨"cat.fake.opaque"⟩)) := by
    native_decide
  simp [opaqueCategoryMatchesCategory, differentIds]

private def validatePersistedRegistryState (state : RegistryState) : Except String Unit := do
  if let some id := state.duplicateEntryId then
    throw s!"duplicate normalized-category registry ID {id}"
  if let some _ := state.duplicateCategoryExpression then
    throw "duplicate normalized-category registry expression"
  if let some spelling := state.duplicatePublicLookupSpelling then
    throw s!"duplicate normalized-category public lookup spelling {spelling}"
  if let some id := duplicateOpaquePortId state.opaquePortIds then
    throw s!"duplicate opaque port ID {id.raw}"
  for category in state.categories do
    let isSelf := match category.expression with
      | .atom id | .opaque id => id == category.id
      | _ => false
    unless categoryIdMatchesExpression category.id category.expression do
      throw s!"category entry {category.id.raw} does not use its own category expression ID"
    unless isSelf ||
        (category.expression.isRegistered state && category.expression.referencesValid state) do
      throw s!"category entry {category.id.raw} has an unresolved registry reference"
    match category.expression with
    | .opaque _ =>
        unless (state.opaqueCategories.filter (opaqueCategoryMatchesCategory category)).size == 1 do
          throw s!"opaque category entry {category.id.raw} has no unique matching companion"
    | _ => pure ()
  for functor in state.functors do
    unless functor.source.isRegistered state && functor.target.isRegistered state &&
        functor.source.referencesValid state && functor.target.referencesValid state &&
        functor.expression.referencesValid state do
      throw s!"functor entry {functor.id.raw} has an unresolved registry reference"
  for classifier in state.classifiers do
    unless classifier.host.isRegistered state && classifier.host.referencesValid state do
      throw s!"classifier entry {classifier.id.raw} has an unresolved registry reference"
  for aliasEntry in state.aliases do
    unless state.categories.any (·.id == aliasEntry.aliasOf) do
      throw s!"alias entry {aliasEntry.id.raw} refers to an unregistered category"
  for opaqueEntry in state.opaqueCategories do
    let some category := state.categories.find? (·.id == opaqueEntry.id)
      | throw s!"opaque category entry {opaqueEntry.id.raw} has no registered category"
    unless opaqueCategoryMatchesCategory category opaqueEntry do
      throw s!"opaque category entry {opaqueEntry.id.raw} does not match its registered category"
    unless opaqueEntry.ports.toList.all fun port =>
        port.source.syntacticEq (.opaque opaqueEntry.id) &&
          port.source.isRegistered state && port.target.isRegistered state do
      throw s!"opaque category entry {opaqueEntry.id.raw} has an invalid port source or endpoint"
  pure ()

private def registryValidationFailed (result : Except String Unit) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

private def persistedOrphanOpaqueExpressionProbeState : RegistryState :=
  { categories := #[{
      id := ⟨"probe.persisted.orphan"⟩, canonicalName := "probe.persisted.orphan",
      declaration := ``sameEndpoint, expression := .opaque ⟨"probe.persisted.orphan"⟩,
      realization := ``sameEndpoint }] }

example : registryValidationFailed
    (validatePersistedRegistryState persistedOrphanOpaqueExpressionProbeState) := by
  decide

private def persistedWrongOpaquePortOwnerProbeState : RegistryState :=
  { categories := #[{
      id := ⟨"probe.persisted.owner"⟩, canonicalName := "probe.persisted.owner",
      declaration := ``sameEndpoint, expression := .opaque ⟨"probe.persisted.owner"⟩,
      realization := ``sameEndpoint }]
    opaqueCategories := #[{
      id := ⟨"probe.persisted.owner"⟩, declaration := ``sameEndpoint,
      realization := ``sameEndpoint,
      ports := #[StructuralPortEntry.mk ⟨"probe.persisted.port"⟩
        (.atom ⟨"probe.persisted.owner"⟩) (.atom ⟨"probe.persisted.owner"⟩)
        ``sameEndpoint ``sameEndpoint "probe"],
      reason := "probe" }] }

example : registryValidationFailed
    (validatePersistedRegistryState persistedWrongOpaquePortOwnerProbeState) := by
  native_decide

private def importedWrongOpaquePortOwnerProbeEntries : Array (Array RegistryEntry) := #[
  #[RegistryEntry.category {
    id := ⟨"probe.imported.owner"⟩, canonicalName := "probe.imported.owner",
    declaration := ``sameEndpoint, expression := .opaque ⟨"probe.imported.owner"⟩,
    realization := ``sameEndpoint }],
  #[RegistryEntry.opaque {
    id := ⟨"probe.imported.owner"⟩, declaration := ``sameEndpoint,
    realization := ``sameEndpoint,
    ports := #[StructuralPortEntry.mk ⟨"probe.imported.port"⟩
      (.atom ⟨"probe.imported.owner"⟩) (.atom ⟨"probe.imported.owner"⟩)
      ``sameEndpoint ``sameEndpoint "probe"],
    reason := "probe" }]]

example : registryValidationFailed
    (validatePersistedRegistryState
      (mkStateFromImportedEntries RegistryState.apply {} importedWrongOpaquePortOwnerProbeEntries)) := by
  native_decide

private initialize registryExt : SimplePersistentEnvExtension RegistryEntry RegistryState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := RegistryState.apply
    addImportedFn := fun as =>
      let state := mkStateFromImportedEntries RegistryState.apply {} as
      match validatePersistedRegistryState state with
      | .error message => panic! s!"invalid normalized-category registry in imported modules: {message}"
      | .ok () => state
}

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

def validateRefinementDeclarationRealization (state : RegistryState)
    (expression : CategoryExpr) (declaration refinement : Name) : MetaM Unit := do
  let (expectedBase, expectedClassifier) ← match expression with
    | .refine base classifier => pure (base, classifier)
    | _ => throwError "refinement realization is attached to a non-refinement expression"
  let refinementConstant ← mkConstWithFreshMVarLevels refinement
  let refinementType ← inferType refinementConstant
  forallTelescopeReducing refinementType fun arguments refinementResult => do
    let refinementArgs := refinementResult.getAppArgs
    unless refinementArgs.size == 2 do
      throwError "refinement realization {refinement} has malformed parameters"
    unless ← withTransparency .all <| isDefEq (Lean.toExpr expression) refinementArgs[0]! do
      throwError "refinement realization {refinement} has the wrong expression"
    let declarationValue ← mkConstWithFreshMVarLevels declaration
    let declarationValue := mkAppN declarationValue arguments
    unless ← withTransparency .all <| isDefEq declarationValue refinementArgs[1]! do
      throwError "refinement declaration {declaration} has the wrong category"
    let refinementValue := mkAppN refinementConstant arguments
    let base ← withTransparency .all do
      mkAppM ``LeanCategories.RefinementRealization.base #[refinementValue]
    let classifierId ← withTransparency .all do
      mkAppM ``LeanCategories.RefinementRealization.classifierId #[refinementValue]
    unless ← withTransparency .all <| isDefEq base (Lean.toExpr expectedBase) do
      throwError "refinement realization {refinement} has the wrong base"
    unless ← withTransparency .all <| isDefEq classifierId (Lean.toExpr expectedClassifier) do
      throwError "refinement realization {refinement} has the wrong classifier"
    let classifier ← withTransparency .all do
      mkAppM ``LeanCategories.RefinementRealization.classifier #[refinementValue]
    let classifierEntry ← match state.classifier? expectedClassifier with
      | some entry => pure entry
      | none => throwError "refinement realization {refinement} has an unregistered classifier"
    let classifierRealization ← withTransparency .all do
      mkAppM ``LeanCategories.RefinementRealization.classifierRealization #[refinementValue]
    let classifierRealizationType ← withTransparency .all <| inferType classifierRealization
    let classifierArgs := classifierRealizationType.getAppArgs
    unless classifierArgs.size == 4 do
      throwError "refinement realization {refinement} has malformed classifier data"
    unless ← withTransparency .all <| isDefEq classifierArgs[0]! (Lean.toExpr classifierEntry.host) do
      throwError "refinement realization {refinement} has the wrong classifier host"
    unless ← withTransparency .all <| isDefEq classifierArgs[1]! (Lean.toExpr expectedClassifier) do
      throwError "refinement realization {refinement} has the wrong classifier ID"
    let registeredConstant ← mkConstWithFreshMVarLevels classifierEntry.realization
    let registeredType ← inferType registeredConstant
    let (registeredParameters, _, _) ← forallMetaTelescopeReducing registeredType
    let registeredValue := mkAppN registeredConstant registeredParameters
    unless ← withTransparency .all <| isDefEq classifierRealization registeredValue do
      throwError "refinement realization {refinement} is not the exact registered classifier realization"
    let baseCategory ← withTransparency .all do
      mkAppM ``LeanCategories.RefinementRealization.baseCategory #[refinementValue]
    let baseRealization ← withTransparency .all do
      mkAppM ``LeanCategories.RefinementRealization.baseRealization #[refinementValue]
    validateCategoryEndpointRealization state expectedBase baseCategory baseRealization
    let hostRealization ← withTransparency .all do
      mkAppM ``LeanCategories.ClassifierRealization.hostRealization #[classifierRealization]
    validateCategoryEndpointRealization state classifierEntry.host classifierArgs[2]!
      hostRealization
    let totalRealization ← withTransparency .all do
      mkAppM ``LeanCategories.ClassifierRealization.totalRealization #[classifierRealization]
    validateClassifierTotalEndpointRealization state expectedClassifier classifierArgs[3]!
      totalRealization
    let baseToHost ← withTransparency .all do
      mkAppM ``LeanCategories.RefinementRealization.baseToHost #[refinementValue]
    let reindexed ← withTransparency .all do
      mkAppM ``LeanCategories.RefinementRealization.reindexed #[refinementValue]
    let expectedReindexed ← withTransparency .all do
      mkAppM ``LeanCategories.Classifier.reindex #[baseToHost, classifier]
    unless ← withTransparency .all <| isDefEq reindexed expectedReindexed do
      throwError "refinement realization {refinement} does not use Classifier.reindex"

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
    | .refine base classifier =>
        validateRefinementEndpointRealization state base classifier
    | .atom _ | .familyApp .. | .opaque _ => pure ()
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

def FunctorExpr.identity? {source target : CategoryExpr}
    : FunctorExpr source target → Option CategoryExpr
  | .identity category => some category
  | _ => none

inductive FunctorExpr.RegistrationKind
  | identity
  | atomic
  | classifierForget (classifier : ClassifierId) (host : CategoryExpr)
  | opaquePort (port : OpaquePortId)

def FunctorExpr.registrationKind {source target : CategoryExpr} :
    FunctorExpr source target → FunctorExpr.RegistrationKind
  | .identity _ => .identity
  | .atomic _ => .atomic
  | .classifierForget classifier host => .classifierForget classifier host
  | .opaquePort port => .opaquePort port

def validateFunctorDeclarationRealization (state : RegistryState) {source target : CategoryExpr}
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
    match expression.registrationKind with
    | .identity => do
        unless ← withTransparency .all <| isDefEq sourceArgs[1]! targetArgs[1]! do
          throwError "identity functor has distinct realized endpoint categories"
        let expectedIdentity ← withTransparency .all do
          mkAppM ``CategoryTheory.CategoryStruct.id #[sourceArgs[1]!]
        unless ← withTransparency .all <| isDefEq declarationValue expectedIdentity do
          throwError "identity functor declaration is not the endpoint identity"
    | .atomic => pure ()
    | .classifierForget classifier host => do
        let classifierEntry ← match state.classifier? classifier with
          | some entry => pure entry
          | none => throwError "classifier forget {classifier.raw} has no registered classifier"
        unless host.syntacticEq classifierEntry.host do
          throwError "classifier forget {classifier.raw} has the wrong symbolic host"
        let classifierConstant ← mkConstWithFreshMVarLevels classifierEntry.realization
        let classifierType ← inferType classifierConstant
        let (parameters, _, _) ← forallMetaTelescopeReducing classifierType
        let classifierValue := mkAppN classifierConstant parameters
        let registeredForgetfulRealization ← withTransparency .all do
          mkAppM ``LeanCategories.ClassifierRealization.forgetfulRealization #[classifierValue]
        unless ← withTransparency .all <| isDefEq realizationValue registeredForgetfulRealization do
          throwError
            "classifier forget {classifier.raw} is not the exact registered classifier forgetful realization"
    | .opaquePort port => do
            let portEntry ← match state.opaquePort? port with
          | some entry => pure entry
          | none => throwError "opaque port {port.raw} has no registered port declaration"
            unless portEntry.source.syntacticEq source && portEntry.target.syntacticEq target do
              throwError "opaque port {port.raw} has the wrong symbolic endpoints"
            unless declaration == portEntry.declaration && realization == portEntry.realization do
              throwError "opaque port {port.raw} is not its exact registered declaration and realization"
            validateOpaquePortRealization state portEntry
    validateCategoryEndpointRealization state source sourceArgs[1]! sourceRealization
    validateCategoryEndpointRealization state target targetArgs[1]! targetRealization
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

private def classifierForgetConstantProbeHost : CategoryExpr := .atom ⟨"probe.classifier.host"⟩
private def classifierForgetConstantProbeId : ClassifierId := ⟨"probe.classifier"⟩

private noncomputable def classifierForgetConstantProbeCategory : ObjCat :=
  CategoryTheory.Cat.of (CategoryTheory.Discrete Bool)

private noncomputable def classifierForgetConstantProbeHostRealization :
    CategoryRealization classifierForgetConstantProbeHost
      classifierForgetConstantProbeCategory := {}

private noncomputable def classifierForgetConstantProbeClassifier :
    Classifier classifierForgetConstantProbeCategory :=
  { total := classifierForgetConstantProbeCategory
    forget := CategoryTheory.CategoryStruct.id _ }

private noncomputable def classifierForgetConstantProbeClassifierRealization :
    ClassifierRealization classifierForgetConstantProbeHost classifierForgetConstantProbeId
      classifierForgetConstantProbeCategory classifierForgetConstantProbeClassifier :=
  { hostRealization := classifierForgetConstantProbeHostRealization
    totalRealization := {} }

private noncomputable def classifierForgetConstantProbeFunctor :
    classifierForgetConstantProbeCategory ⟶ classifierForgetConstantProbeCategory :=
  (CategoryTheory.Functor.const (CategoryTheory.Discrete Bool)).obj
    (CategoryTheory.Discrete.mk true)
    |>.toCatHom

private noncomputable def classifierForgetConstantProbeFunctorRealization :
    FunctorRealization
      (.classifierForget classifierForgetConstantProbeId classifierForgetConstantProbeHost)
      classifierForgetConstantProbeCategory classifierForgetConstantProbeCategory
      classifierForgetConstantProbeFunctor :=
  { sourceRealization := {}
    targetRealization := classifierForgetConstantProbeHostRealization }

private def classifierForgetConstantProbeState : RegistryState :=
  { categories := #[{
      id := ⟨"probe.classifier.host"⟩
      canonicalName := "probe.classifier.host"
      declaration := ``classifierForgetConstantProbeCategory
      expression := classifierForgetConstantProbeHost
      realization := ``classifierForgetConstantProbeHostRealization}]
    classifiers := #[{
      id := classifierForgetConstantProbeId
      canonicalName := "probe.classifier"
      declaration := ``classifierForgetConstantProbeClassifier
      host := classifierForgetConstantProbeHost
      realization := ``classifierForgetConstantProbeClassifierRealization}] }

run_cmd
  liftTermElabM do
    let accepted ← try
        validateFunctorDeclarationRealization classifierForgetConstantProbeState
          (.classifierForget classifierForgetConstantProbeId classifierForgetConstantProbeHost)
          ``classifierForgetConstantProbeFunctor
          ``classifierForgetConstantProbeFunctorRealization
        pure true
      catch _ => pure false
    if accepted then
      throwError "constant classifier-forget probe was accepted"

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
  | .discrete, .commRingNat => do
      let canonicalTransport ← withTransparency .all do
        mkAppM ``LeanCategories.CategoryFamilyRealization.canonicalDiscreteCommRingNatTransport
          #[realizationValue]
      unless ← withTransparency .all <| isDefEq transportValue canonicalTransport do
        throwError
          "registry equality-only transport is not the canonical discrete family transport"
  | .discrete, .domain => do
      let canonicalTransport ← withTransparency .all do
        mkAppM ``LeanCategories.CategoryFamilyRealization.canonicalDiscreteDomainTransport
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
    let stateWithClassifier :=
      { _state with classifiers := _state.classifiers.push entry }
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
  let state := registryExt.getState (← getEnv)
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
      match e.expression, e.refinementRealization with
      | .refine .., some refinement =>
          validateRefinementDeclarationRealization state e.expression e.declaration refinement
      | .refine .., none =>
          throwError "refinement category {e.id.raw} has no typed RefinementRealization"
      | _, some _ =>
          throwError "non-refinement category {e.id.raw} carries a refinement realization"
      | _, none => pure ()
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
      ensureCategoryRealization e.realization
      validateCategoryDeclarationRealization state (.opaque e.id) e.declaration e.realization none
      for port in e.ports do
        ensureFunctorDeclaration port.declaration
        ensureFunctorRealization port.realization
        validateOpaquePortRealization state port

/- Validate the elaborated declaration and persist exactly one registry entry. -/
def addRegistryEntryChecked (entry : RegistryEntry) : MetaM Unit := do
  validateRegistryEntryDeclaration entry
  let env ← getEnv
  let state := registryExt.getState env
  if state.hasEntryId entry then
    throwError "duplicate normalized-category registry ID: {entry.stableId}"
  match entry with
  | .category e =>
      if state.categories.any fun existing =>
          existing.expression.syntacticEq e.expression then
        throwError "duplicate normalized-category registry expression"
  | _ => pure ()
  match entry.publicLookupSpelling with
  | some spelling =>
      if state.publicLookupSpellings.any (· == spelling) then
        throwError "duplicate normalized-category public lookup spelling: {spelling}"
  | none => pure ()
  match entry with
  | .category e =>
      unless categoryIdMatchesExpression e.id e.expression do
        throwError "category entry {e.id.raw} does not use its own category expression ID"
      let isSelf := match e.expression with
        | .atom id | .opaque id => id == e.id
        | _ => false
      if (!e.expression.isRegistered state && !isSelf) || !e.expression.referencesValid state then
        throwError "category entry {e.id.raw} has an unresolved or ill-typed functor reference"
  | .functor e =>
      if !e.source.isRegistered state || !e.target.isRegistered state ||
          !e.source.referencesValid state || !e.target.referencesValid state ||
          !e.expression.referencesValid state then
        throwError "functor entry {e.id.raw} has an unresolved or unregistered endpoint"
  | .classifier e =>
      unless e.host.isRegistered state && e.host.referencesValid state do
        throwError "classifier entry {e.id.raw} has an unresolved or unregistered host"
  | .alias e =>
      unless state.categories.any (·.id == e.aliasOf) do
        throwError "alias entry {e.id.raw} refers to an unregistered category"
  | .opaque e =>
      let category ← match state.categories.find? (·.id == e.id) with
        | some category => pure category
        | none => throwError "opaque category entry {e.id.raw} has no registered category"
      unless opaqueCategoryMatchesCategory category e do
        throwError "opaque category entry {e.id.raw} does not match its registered category"
      unless e.realization == category.realization do
        throwError "opaque category entry {e.id.raw} does not use its registered realization"
      for port in e.ports do
        unless port.source.syntacticEq (.opaque e.id) do
          throwError "opaque port {port.id.raw} is owned by another opaque category"
        unless port.source.isRegistered state && port.target.isRegistered state do
          throwError "opaque port {port.id.raw} has an unregistered endpoint"
      match duplicateOpaquePortId (e.ports.toList.map (·.id)) with
      | some id => throwError "duplicate opaque port ID {id.raw}"
      | none => pure ()
      for category in state.opaqueCategories do
        for port in e.ports do
          unless !category.ports.any fun registered => registered.id == port.id do
            throwError "duplicate opaque port ID {port.id.raw}"
  | _ => pure ()
  for declaration in entry.declarations do
    if declaration.isAnonymous then
      throwError "registry entry {entry.stableId} has no declaration name"
    if (env.find? declaration).isNone then
      throwError "registry entry {entry.stableId} refers to unknown declaration {declaration}"
  modifyEnv (registryExt.addEntry · entry)

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

private def registryObject (fields : List (String × Json)) : Json := Json.mkObj fields

structure RegistryManifestParameter where
  ids : Array String
  name : String
  kind : String
  dependency : Option Nat
  deriving DecidableEq, Repr, ToJson, FromJson

inductive RegistryManifestParameterExpr
  | variable (id : String)
  | apply (operation : String) (argument : RegistryManifestParameterExpr)
  | apply2 (operation : String) (left right : RegistryManifestParameterExpr)
  | apply3 (operation : String)
      (first second third : RegistryManifestParameterExpr)
  deriving DecidableEq, Repr

private def registryManifestParameterExprJson : RegistryManifestParameterExpr → Json
  | .variable id => registryObject [("tag", "variable"), ("id", id)]
  | .apply operation argument => registryObject [
      ("tag", "apply"), ("operation", operation),
      ("argument", registryManifestParameterExprJson argument)]
  | .apply2 operation left right => registryObject [
      ("tag", "apply2"), ("operation", operation),
      ("left", registryManifestParameterExprJson left),
      ("right", registryManifestParameterExprJson right)]
  | .apply3 operation first second third => registryObject [
      ("tag", "apply3"), ("operation", operation),
      ("first", registryManifestParameterExprJson first),
      ("second", registryManifestParameterExprJson second),
      ("third", registryManifestParameterExprJson third)]

instance : ToJson RegistryManifestParameterExpr where
  toJson := registryManifestParameterExprJson

private partial def registryManifestParameterExprOfJson : Json → Except String RegistryManifestParameterExpr :=
  fun j => do
    let tag ← j.getObjValAs? String "tag"
    match tag with
    | "variable" => .variable <$> j.getObjValAs? String "id"
    | "apply" => .apply <$> j.getObjValAs? String "operation" <*> registryManifestParameterExprOfJson (← j.getObjValAs? Json "argument")
    | "apply2" => .apply2 <$> j.getObjValAs? String "operation" <*> registryManifestParameterExprOfJson (← j.getObjValAs? Json "left") <*> registryManifestParameterExprOfJson (← j.getObjValAs? Json "right")
    | "apply3" => .apply3 <$> j.getObjValAs? String "operation" <*> registryManifestParameterExprOfJson (← j.getObjValAs? Json "first") <*> registryManifestParameterExprOfJson (← j.getObjValAs? Json "second") <*> registryManifestParameterExprOfJson (← j.getObjValAs? Json "third")
    | _ => throw s!"unknown parameter expression tag: {tag}"

instance : FromJson RegistryManifestParameterExpr where
  fromJson? := registryManifestParameterExprOfJson

inductive RegistryManifestCategoryExpr
  | atom (id : String)
  | familyApp (family : String) (args : Array RegistryManifestParameterExpr)
  | classifierTotal (classifier : String)
  | refine (base : RegistryManifestCategoryExpr) (classifier : String)
  | opaque (id : String)
  deriving DecidableEq, Repr

private def registryManifestCategoryExprJson : RegistryManifestCategoryExpr → Json
  | .atom id => registryObject [("tag", "atom"), ("id", id)]
  | .familyApp family args => registryObject [
      ("tag", "familyApp"), ("family", family), ("args", toJson args)]
  | .classifierTotal classifier => registryObject [
      ("tag", "classifierTotal"), ("classifier", classifier)]
  | .refine base classifier => registryObject [
      ("tag", "refine"), ("base", registryManifestCategoryExprJson base),
      ("classifier", classifier)]
  | .opaque id => registryObject [("tag", "opaque"), ("id", id)]

instance : ToJson RegistryManifestCategoryExpr where
  toJson := registryManifestCategoryExprJson

private partial def registryManifestCategoryExprOfJson : Json → Except String RegistryManifestCategoryExpr :=
  fun j => do
    let tag ← j.getObjValAs? String "tag"
    match tag with
    | "atom" => .atom <$> j.getObjValAs? String "id"
    | "familyApp" => .familyApp <$> j.getObjValAs? String "family" <*> j.getObjValAs? _ "args"
    | "classifierTotal" => .classifierTotal <$> j.getObjValAs? String "classifier"
    | "refine" => .refine <$> registryManifestCategoryExprOfJson (← j.getObjValAs? Json "base") <*> j.getObjValAs? String "classifier"
    | "opaque" => .opaque <$> j.getObjValAs? String "id"
    | _ => throw s!"unknown category expression tag: {tag}"

instance : FromJson RegistryManifestCategoryExpr where
  fromJson? := registryManifestCategoryExprOfJson

inductive RegistryManifestFunctorExpr
  | identity (category : RegistryManifestCategoryExpr)
  | atomic (id : String)
  | classifierForget (classifier : String) (host : RegistryManifestCategoryExpr)
  | opaquePort (id : String)
  deriving DecidableEq, Repr

instance : ToJson RegistryManifestFunctorExpr where
  toJson
    | .identity category => registryObject [("tag", "identity"), ("category", toJson category)]
    | .atomic id => registryObject [("tag", "atomic"), ("id", id)]
    | .classifierForget classifier host => registryObject [
        ("tag", "classifierForget"), ("classifier", classifier), ("host", toJson host)]
    | .opaquePort id => registryObject [("tag", "opaquePort"), ("id", id)]

instance : FromJson RegistryManifestFunctorExpr where
  fromJson? j := do
    let tag ← j.getObjValAs? String "tag"
    match tag with
    | "identity" => .identity <$> j.getObjValAs? _ "category"
    | "atomic" => .atomic <$> j.getObjValAs? String "id"
    | "classifierForget" =>
        .classifierForget <$> j.getObjValAs? String "classifier" <*> j.getObjValAs? _ "host"
    | "opaquePort" => .opaquePort <$> j.getObjValAs? String "id"
    | _ => throw s!"unknown functor expression tag: {tag}"

structure RegistryManifestCategory where
  id : String
  canonicalName : String
  declaration : String
  realization : String
  refinementRealization : String
  expression : RegistryManifestCategoryExpr
  deriving DecidableEq, Repr, ToJson, FromJson

structure RegistryManifestFamily where
  id : String
  canonicalName : String
  schema : String
  realization : String
  transport : String
  parameters : Array RegistryManifestParameter
  variance : String
  deriving DecidableEq, Repr, ToJson, FromJson

structure RegistryManifestAlias where
  id : String
  spelling : String
  aliasOf : String
  declaration : String
  realization : String
  deriving DecidableEq, Repr, ToJson, FromJson

structure RegistryManifestClassifier where
  id : String
  canonicalName : String
  host : RegistryManifestCategoryExpr
  declaration : String
  realization : String
  deriving DecidableEq, Repr, ToJson, FromJson

structure RegistryManifestFunctor where
  id : String
  canonicalName : String
  source : RegistryManifestCategoryExpr
  target : RegistryManifestCategoryExpr
  declaration : String
  realization : String
  expression : RegistryManifestFunctorExpr
  deriving DecidableEq, Repr, ToJson, FromJson

structure RegistryManifestPort where
  id : String
  source : RegistryManifestCategoryExpr
  target : RegistryManifestCategoryExpr
  declaration : String
  realization : String
  provenance : String
  deriving DecidableEq, Repr, ToJson, FromJson

structure RegistryManifestOpaque where
  id : String
  declaration : String
  realization : String
  reason : String
  ports : Array RegistryManifestPort
  deriving DecidableEq, Repr, ToJson, FromJson

structure RegistryManifest where
  schemaVersion : String
  categories : Array RegistryManifestCategory
  classifiers : Array RegistryManifestClassifier
  functors : Array RegistryManifestFunctor
  aliases : Array RegistryManifestAlias
  opaqueCategories : Array RegistryManifestOpaque
  categoryFamilies : Array RegistryManifestFamily
  source : String
  deriving DecidableEq, Repr, ToJson, FromJson

private def registryManifestParameterExpr : ParameterExpr → RegistryManifestParameterExpr
  | .variable id => .variable id.raw
  | .apply operation argument => .apply operation.raw (registryManifestParameterExpr argument)
  | .apply2 operation left right =>
      .apply2 operation.raw (registryManifestParameterExpr left) (registryManifestParameterExpr right)
  | .apply3 operation first second third =>
      .apply3 operation.raw (registryManifestParameterExpr first)
        (registryManifestParameterExpr second) (registryManifestParameterExpr third)

private def registryManifestCategoryExpr : CategoryExpr → RegistryManifestCategoryExpr
  | .atom id => .atom id.raw
  | .familyApp family args => .familyApp family.raw (args.map registryManifestParameterExpr)
  | .classifierTotal classifier => .classifierTotal classifier.raw
  | .refine base classifier => .refine (registryManifestCategoryExpr base) classifier.raw
  | .opaque id => .opaque id.raw

private def registryManifestFunctorExpr {source target : CategoryExpr} :
    FunctorExpr source target → RegistryManifestFunctorExpr
  | .identity category => .identity (registryManifestCategoryExpr category)
  | .atomic id => .atomic id.raw
  | .classifierForget classifier host =>
      .classifierForget classifier.raw (registryManifestCategoryExpr host)
  | .opaquePort id => .opaquePort id.raw

private def registryManifestSchema : CategoryFamilySchema → String
  | .ring => "ring"
  | .commRing => "commRing"
  | .commRingModule => "commRingModule"
  | .commRingNat => "commRingNat"
  | .domain => "domain"

private def registryManifest (state : RegistryState) : RegistryManifest :=
  let cats := state.categories.qsort (fun a b => a.id.raw < b.id.raw)
  let families := state.categoryFamilies.qsort (fun a b => a.id.raw < b.id.raw)
  let clfs := state.classifiers.qsort (fun a b => a.id.raw < b.id.raw)
  let functors := state.functors.qsort (fun a b => a.id.raw < b.id.raw)
  let aliases := state.aliases.qsort (fun a b => a.id.raw < b.id.raw)
  let opaqueEntries := state.opaqueCategories.qsort (fun a b => a.id.raw < b.id.raw)
  { schemaVersion := "0.2.0-ids"
    categories := cats.map fun e => {
      id := e.id.raw, canonicalName := e.canonicalName, declaration := e.declaration.toString,
      realization := e.realization.toString,
      refinementRealization := e.refinementRealization.map Lean.Name.toString |>.getD "",
      expression := registryManifestCategoryExpr e.expression }
    classifiers := clfs.map fun e => {
      id := e.id.raw, canonicalName := e.canonicalName,
      host := registryManifestCategoryExpr e.host, declaration := e.declaration.toString,
      realization := e.realization.toString }
    functors := functors.map fun e => {
      id := e.id.raw, canonicalName := e.canonicalName,
      source := registryManifestCategoryExpr e.source, target := registryManifestCategoryExpr e.target,
      declaration := e.declaration.toString, realization := e.realization.toString,
      expression := registryManifestFunctorExpr e.expression }
    aliases := aliases.map fun e => {
      id := e.id.raw, spelling := e.spelling, aliasOf := e.aliasOf.raw,
      declaration := e.declaration.toString, realization := e.realization.toString }
    opaqueCategories := opaqueEntries.map fun e => {
      id := e.id.raw, declaration := e.declaration.toString, realization := e.realization.toString,
      reason := e.reason,
      ports := e.ports.map fun p => {
        id := p.id.raw, source := registryManifestCategoryExpr p.source,
        target := registryManifestCategoryExpr p.target, declaration := p.declaration.toString,
        realization := p.realization.toString, provenance := p.provenance } }
    categoryFamilies := families.map fun e => {
      id := e.id.raw, canonicalName := e.canonicalName,
      schema := registryManifestSchema e.schema,
      realization := e.realization.toString, transport := e.transport.toString,
      parameters := e.schema.parameterMetadata.map fun parameter => {
        ids := parameter.ids.toArray.map (·.raw), name := parameter.name,
        kind := parameter.kind.raw, dependency := parameter.dependency },
      variance := e.transportSemantics.variance.raw }
    source := "lean-registry" }

private def registryManifestJson (state : RegistryState) : Json := toJson (registryManifest state)

/-- Return the manifest produced from the checked persistent registry state. -/
def checkedRegistryManifestDTO : CoreM RegistryManifest := do
  let state := registryExt.getState (← getEnv)
  match validatePersistedRegistryState state with
  | .error message => throwError message
  | .ok () => pure (registryManifest state)

def checkedRegistryManifest : CoreM Json := do
  return toJson (← checkedRegistryManifestDTO)

end LeanCategories

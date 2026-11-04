/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue
public meta import LeanCategories.Catalogue

@[expose] public section

/-!
# The registry snapshot contract (#49)

Checks the three things a downstream consumer relies on: a stable ID resolves to the checked
row and its Lean declaration; the fold accepts rows it has not seen; and the fold is
fail-loud on a re-registered ID or an unresolved reference, so a consumer cannot silently
overwrite checked meaning or invent a dangling route.
-/

namespace CasCatalogue.RegistrySnapshotTests

open CasCatalogue

open Lean Meta in
run_meta do
  let snap ← RegistrySnapshot.snapshot
  unless snap.entries.size > 0 do
    throwError "the registry snapshot is empty; a consumer would read no rows"
  -- Stage 1: registry rows resolve by stable ID, and the row names a real declaration.
  let some names := snap.declarationNames? "cat.sets"
    | throwError "the snapshot does not resolve the stable ID cat.sets"
  unless names.size > 0 do
    throwError "cat.sets names no declaration"
  for name in names do
    unless (← getEnv).contains name do
      throwError "cat.sets names the absent declaration {name}"
  let some functorNames := snap.declarationNames? "fun.sets.list"
    | throwError "the snapshot does not resolve the stable ID fun.sets.list"
  unless functorNames.size > 0 do
    throwError "fun.sets.list names no declaration"
  -- A consumer resolves by ID alone, without a generated mapping or a seed file.
  unless (snap.idsWithPrefix "fun.").size > 0 do
    throwError "the snapshot exposes no functor rows by prefix"
  -- An empty fold is accepted: the snapshot is internally consistent.
  match snap.validateDerived #[] with
  | .ok () => pure ()
  | .error message => throwError "the checked snapshot fails its own fold check: {message}"
  -- Fail-loud: a derived row may not re-register a checked stable ID.
  let some row := snap.findEntry? "cat.sets"
    | throwError "the snapshot does not expose cat.sets"
  match snap.validateDerived #[row] with
  | .ok () => throwError "the fold accepted a re-registration of cat.sets"
  | .error _ => pure ()
  -- Fail-loud: a derived row may not leave a reference unresolved.
  let some (.cell cell) := snap.findEntry? "cell.sets.list.unit"
    | throwError "cell.sets.list.unit is not a cell row"
  let dangling := SemanticEntry.cell { cell with left := #[.functor ⟨"fun.unresolved_probe"⟩] }
  match validateEntries #[dangling] with
  | .ok () => throwError "the fold accepted a cell row naming an unregistered functor"
  | .error _ => pure ()
  -- Fail-loud on every reference family the entry types carry, not just the ones the
  -- persisted-state gate happens to cover. Each probe mutates one reference of a real row.
  let expectDangling (label : String) (entries : Array SemanticEntry) : MetaM Unit := do
    match validateEntries entries with
    | .ok () => throwError "the fold accepted {label}"
    | .error _ => pure ()
  let some inc := snap.entries.findSome? (fun e => match e with
      | .inclusion x => some x
      | _ => none)
    | throwError "no inclusion row to probe"
  expectDangling "an inclusion over an unregistered superobject"
    #[.inclusion { inc with super := ⟨"obj.unregistered_probe"⟩ }]
  expectDangling "an inclusion over an unregistered subobject"
    #[.inclusion { inc with sub := ⟨"obj.unregistered_probe"⟩ }]
  let some power := snap.entries.findSome? (fun e => match e with
      | .powerObject x => some x
      | _ => none)
    | throwError "no power-object row to probe"
  expectDangling "a power object over an unregistered object"
    #[.powerObject { power with object := ⟨"obj.unregistered_probe"⟩ }]
  expectDangling "a power object over an unregistered truth object"
    #[.powerObject { power with omega := ⟨"obj.unregistered_probe"⟩ }]
  let some operation := snap.entries.findSome? (fun e => match e with
      | .operation x => some x
      | _ => none)
    | throwError "no operation row to probe"
  let opRefines : OperationRefinement :=
    { base := ⟨"op.unregistered_probe"⟩, route := #[], identification := operation.declaration }
  expectDangling "an operation refining an unregistered operation"
    #[.operation { operation with refines := some opRefines }]
  let some object := snap.entries.findSome? (fun e => match e with
      | .object x => some x
      | _ => none)
    | throwError "no object row to probe"
  let objRefines : ObjectRefinement :=
    { base := ⟨"obj.unregistered_probe"⟩, route := #[], identification := object.declaration }
  expectDangling "an object refining an unregistered base"
    #[.object { object with refines := some objRefines }]
  let some subset := snap.entries.findSome? (fun e => match e with
      | .subsetLiteral x => some x
      | _ => none)
    | throwError "no subset-literal row to probe"
  expectDangling "a subset literal over an unregistered power object"
    #[.subsetLiteral { subset with powerObject := ⟨"pow.unregistered_probe"⟩ }]
  let some presentation := snap.entries.findSome? (fun e => match e with
      | .presentation x => some x
      | _ => none)
    | throwError "no presentation row to probe"
  expectDangling "a presentation over an unregistered source object"
    #[.presentation { presentation with source := ⟨"obj.unregistered_probe"⟩ }]
  let some numeral := snap.entries.findSome? (fun e => match e with
      | .numeral x => some x
      | _ => none)
    | throwError "no numeral row to probe"
  expectDangling "a numeral over an unregistered category"
    #[.numeral { numeral with over := some ⟨"cat.unregistered_probe"⟩ }]
  let some morphism := snap.entries.findSome? (fun e => match e with
      | .morphism x => some x
      | _ => none)
    | throwError "no morphism row to probe"
  expectDangling "a morphism in an unregistered category"
    #[.morphism { morphism with category := ⟨"cat.unregistered_probe"⟩ }]
  let some binder := snap.entries.findSome? (fun e => match e with
      | .binder x => some x
      | _ => none)
    | throwError "no binder row to probe"
  expectDangling "a binder in an unregistered category"
    #[.binder { binder with category := ⟨"cat.unregistered_probe"⟩ }]
  expectDangling "an operation in an unregistered category"
    #[.operation { operation with category := ⟨"cat.missing"⟩ }]
  let some method := snap.entries.findSome? (fun e => match e with
      | .method x => some x
      | _ => none)
    | throwError "no method row to probe"
  expectDangling "a method owned by an unregistered category"
    #[.method { method with owner := .atom ⟨"cat.unregistered_probe"⟩ }]
  let some limit := snap.entries.findSome? (fun e => match e with
      | .limit x => some x
      | _ => none)
    | throwError "no limit row to probe"
  expectDangling "a limit in an unregistered category"
    #[.limit { limit with category := ⟨"cat.unregistered_probe"⟩ }]
  -- A nonempty derived fold that references only registered rows is accepted: the check is
  -- reference completeness, not a blanket refusal of consumer rows.
  let derived : SemanticEntry := .morphism
    { id := ⟨"mor.sets.registry_snapshot_probe"⟩, category := ⟨"cat.sets"⟩,
      name := "registry_snapshot_probe", declaration := `id }
  match snap.validateDerived #[derived] with
  | .ok () => pure ()
  | .error message => throwError "the fold refused a well-referenced derived row: {message}"
  -- Two derived rows with the same stable ID are refused, even though neither is in the
  -- snapshot: the fold is fail-loud within itself as well as against the registry.
  match snap.validateDerived #[derived, derived] with
  | .ok () => throwError "the fold accepted two derived rows with the same stable ID"
  | .error _ => pure ()

end CasCatalogue.RegistrySnapshotTests

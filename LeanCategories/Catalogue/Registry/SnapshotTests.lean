/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.Snapshot
public meta import LeanCategories.Catalogue.Registry.Snapshot
public import LeanCategories.Catalogue.Semantics.Foundation.Lists

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

end CasCatalogue.RegistrySnapshotTests

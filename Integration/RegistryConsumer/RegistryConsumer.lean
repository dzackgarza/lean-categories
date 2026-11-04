/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Registry.Snapshot

/-!
# A minimal downstream consumer of the lean-categories registry (#49)

This package is the demonstrated consumer of a pinned `lean-categories` revision. It requires
the library as a Lake dependency on the same toolchain and Mathlib pin, and reads the registry
snapshot at elaboration time.

It resolves rows by stable ID only. It imports no generated Sage mapping, no Python seed, no
hand-authored DOT file and no research branch artifact, and it owns no mathematics: every row
it uses is a checked row of the pinned revision, and the declaration that row names is the
meaning of the ID.

The downstream contract it exercises is the one `#49` fixes:

* stage 1 rows (`cat.`, `fun.`, `cell.`, `obj.`, `op.`, `mor.` …) resolve by stable ID;
* rows it re-registers or derives fold through `RegistrySnapshot.validateDerived`, which
  refuses a stable ID that already exists and refuses an unresolved reference.
-/

open Lean

/-- The stable IDs this consumer resolves out of the pinned revision. -/
def resolvedIds : List String := ["cat.sets", "fun.sets.list", "cell.sets.list.unit"]

open Lean Meta in
run_meta do
  let snap ← CasCatalogue.RegistrySnapshot.snapshot
  for id in resolvedIds do
    unless snap.hasEntry id do
      throwError "the pinned registry does not expose the stable ID {id}"
    let some names := snap.declarationNames? id
      | throwError "the pinned registry resolves no declaration for {id}"
    unless names.size > 0 do
      throwError "{id} names no declaration"
    for name in names do
      unless (← getEnv).contains name do
        throwError "{id} names the absent declaration {name}"
  -- A consumer fold may add rows but may not overwrite a checked one.
  let row? : Option CasCatalogue.SemanticEntry :=
    CasCatalogue.RegistrySnapshot.findEntry? snap "cat.sets"
  let row ← match row? with
    | some row => pure row
    | none => throwError "the pinned registry does not expose cat.sets"
  match CasCatalogue.RegistrySnapshot.validateDerived snap #[row] with
  | Except.ok () => throwError "the consumer fold accepted a re-registration of cat.sets"
  | Except.error _ => pure ()

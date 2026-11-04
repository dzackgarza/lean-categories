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

/-- The stable-ID layers a release must expose, with the names the contract gives them. -/
def requiredLayers : List (String × String) :=
  [("cat.", "category"), ("fun.", "functor"), ("cell.", "cell"), ("obj.", "object"),
   ("op.", "operation"), ("mor.", "morphism")]

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
      -- The resolved declaration is a declaration of this library, not a name the consumer
      -- invented: resolution goes ID → checked row → library declaration.
      let rendered := toString name
      unless rendered.startsWith "CasCatalogue." || rendered.startsWith "LeanCategories." do
        throwError "{id} resolved to {rendered}, which is not a declaration of the library"
  -- A category row carries both its declaration and its realization: resolution returns the
  -- row's actual declarations rather than a single conventional name.
  let some setNames := snap.declarationNames? "cat.sets"
    | throwError "the pinned registry resolves no declaration for cat.sets"
  unless setNames.size >= 2 do
    throwError "cat.sets resolved to {setNames.size} declaration(s); a category row names its \
      declaration and its realization"
  -- Each layer of the named surface is populated by the pinned revision.
  for layer in requiredLayers do
    unless (snap.idsWithPrefix layer.1).size > 0 do
      throwError "the pinned revision exposes no {layer.2} rows"
  -- Lookup is a real lookup, not a constant-true stub: an ID the revision does not carry is
  -- absent, and the fold refuses derived rows that reference it.
  if snap.hasEntry "cat.does_not_exist" then
    throwError "lookup reported a category the pinned revision does not carry"
  -- A consumer fold may add rows but may not overwrite a checked one.
  let row? : Option CasCatalogue.SemanticEntry :=
    CasCatalogue.RegistrySnapshot.findEntry? snap "cat.sets"
  let row ← match row? with
    | some row => pure row
    | none => throwError "the pinned registry does not expose cat.sets"
  match CasCatalogue.RegistrySnapshot.validateDerived snap #[row] with
  | Except.ok () => throwError "the consumer fold accepted a re-registration of cat.sets"
  | Except.error _ => pure ()
  -- A derived row that references an unregistered category is refused, so a consumer cannot
  -- hang an ownership edge on a row the pinned revision does not carry.
  let derived : CasCatalogue.SemanticEntry := .morphism
    { id := ⟨"mor.sets.consumer_probe"⟩, category := ⟨"cat.does_not_exist"⟩,
      name := "consumer_probe", declaration := `id }
  match CasCatalogue.RegistrySnapshot.validateDerived snap #[derived] with
  | Except.ok () => throwError "the consumer fold accepted a row over an unregistered category"
  | Except.error _ => pure ()

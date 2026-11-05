/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# The registry snapshot: the downstream consumption surface (#49)

`RegistrySnapshot` is the read-only, checked view of the semantic registry that a downstream
Lake dependency consumes. A consumer reads it at elaboration time and resolves rows by stable
ID; it never reconstructs a category, functor, constructor or method graph from a generated
Sage mapping, a Python seed, a hand-authored DOT file or a research branch artifact.

Consumption is staged, and each release names the stages it supports:

1. **registry rows** — every checked entry, resolvable by stable ID through `findEntry?`,
   `hasEntry` and `declarationNames?`;
2. **typed expressions** — the `CategoryExpr`/`FunctorExpr` surface of #31/#54, reachable
   through the expression fields of the rows above;
3. **operation and method rows** — the registered `operation` and `method` entries of
   #28/#53, whose `declaration` is the same checked semantic operation lean-categories uses.

A consumer that re-registers or derives rows folds them through `validateDerived`, which is
fail-loud: a stable ID already present (in the snapshot or earlier in the fold) and any
unresolved registry reference are refused with the offending ID. Rows are never silently
overwritten, and a derived row does not acquire meaning from the consumer that wrote it.
-/

namespace CasCatalogue

/-- A read-only, checked view of the semantic registry. It holds the traced entries of the
current environment; the only write path into a registry remains `addSemanticEntryChecked`
through the `normalized_registry` command. -/
structure RegistrySnapshot where
  /-- Every checked entry of the registry. Entries are grouped by row kind in the registry's
  own field order, and each group is in registration order; the array is **not** a global
  registration-order trace, because the registry state stores one array per row kind. Use
  `idsWithPrefix` or the row kinds for a stable selection, never a global index. -/
  entries : Array SemanticEntry
  deriving Inhabited

namespace RegistrySnapshot

/-- The snapshot of a registry state. -/
def ofState (state : SemanticState) : RegistrySnapshot := ⟨state.entries.toArray⟩

/-- The stable IDs this release exposes, grouped by row kind in the same order as
`RegistrySnapshot.entries`. -/
def stableIds (snap : RegistrySnapshot) : Array String :=
  snap.entries.map SemanticEntry.stableId

/-- The stable IDs of one layer, selected by the stable-ID namespace prefix
(`cat.`, `fun.`, `cell.`, `op.`, `mor.`, `obj.`, …). -/
def idsWithPrefix (snap : RegistrySnapshot) (pre : String) : Array String :=
  (snap.stableIds.filter (·.startsWith pre))

/-- Resolve one checked row by stable ID. -/
def findEntry? (snap : RegistrySnapshot) (id : String) : Option SemanticEntry :=
  snap.entries.find? (fun entry => entry.stableId == id)

/-- Whether the release exposes a row with this stable ID. -/
def hasEntry (snap : RegistrySnapshot) (id : String) : Bool :=
  (snap.findEntry? id).isSome

/-- The Lean declarations a row names, at its own stable ID. A consumer resolves the
declaration through this and imports nothing else: the ID is the surface, the declaration is
the checked meaning. -/
def declarationNames? (snap : RegistrySnapshot) (id : String) : Option (Array Lean.Name) :=
  (snap.findEntry? id).map SemanticEntry.declarations

/-- Fail-loud fold check for rows a consumer re-registers or derives on top of the snapshot.
Refuses a stable ID that already occurs in the snapshot or earlier in the fold, then replays
snapshot and derived rows and refuses any unresolved registry reference. -/
def validateDerived (snap : RegistrySnapshot) (derived : Array SemanticEntry) :
    Except String Unit := do
  let mut seen : List String := snap.stableIds.toList
  for entry in derived.toList do
    let id := entry.stableId
    if seen.contains id then
      throw s!"stable ID {id} is already checked or derived in this fold; \
        a consumer row does not overwrite a checked row"
    seen := id :: seen
  validateEntries (snap.entries ++ derived)

/-- The snapshot of the current environment: the registry a downstream dependency reads at
elaboration time. -/
def snapshot : Lean.CoreM RegistrySnapshot :=
  return ofState (← semanticState)

end RegistrySnapshot

end CasCatalogue

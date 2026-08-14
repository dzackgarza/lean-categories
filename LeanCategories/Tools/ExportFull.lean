/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Tools.ExportJson
public import LeanCategories.Catalogue.Standard
public import Lean.Data.Json
public import Lean.CoreM

public meta import LeanCategories.Tools.ExportJson

@[expose] public section

/-!
# Registry export (`lean-categories-export`)

Emits JSON from the Lean registry. The executable reloads the module that owns
the viability declarations and serializes its persistent environment extension.

Does **not** read external semantic-seed artifacts.
-/

open Lean Elab Command

-- Compile-time: Register must have populated getRegistry with the specimen.
run_cmd
  let manifest ← liftCoreM LeanCategories.checkedRegistryManifest
  let baseline := manifest.compress
  if !(baseline.contains "cat.sets") then
    throwError "checked registry manifest is missing the registered Sets category"
  if !baseline.contains "fam.modules" then
    throwError "checked registry manifest is missing the registered Modules family"
  if !baseline.contains "fun.sets.identity" then
    throwError "checked registry manifest is missing the registered Sets identity functor"

namespace LeanCategories.Tools.ExportFull

open LeanCategories
open Tools

/-- Reload the compiled registry extension; this is the exporter data source. -/
def loadRegisteredManifest : IO Json := do
  let appDir ← IO.appDir
  let buildOleanRoot := appDir.parent.get! / "lib" / "lean"
  let workspaceRoot := appDir.parent.get!.parent.get!.parent.get!
  let packageOleanRoots := [
    "mathlib", "batteries", "Qq", "aesop", "plausible", "LeanSearchClient",
    "proofwidgets", "importGraph",
].map fun package =>
    workspaceRoot / ".lake" / "packages" / package / ".lake" / "build" / "lib" / "lean"
  Lean.initSearchPath (← Lean.findSysroot) (buildOleanRoot :: packageOleanRoots)
  unsafe Lean.enableInitializersExecution
  let env ← Lean.importModules
    #[{ module := `LeanCategories.Catalogue.Standard }] {}
    (loadExts := true)
  let result ← Lean.Core.CoreM.toIO LeanCategories.checkedRegistryManifest
    { fileName := "", options := {}, fileMap := default } { env }
  pure result.1

/-- Validate Lean-authored registry JSON. -/
def validate (j : Json) : Except String Unit := do
  let schema ← j.getObjValAs? String "schemaVersion"
  if schema.isEmpty then
    throw "missing schemaVersion"
  let source ← j.getObjValAs? String "source"
  if source != "lean-registry" then
    throw s!"expected source=lean-registry, got {source}"
  let cats ← j.getObjValAs? (Array Json) "categories"
  let aliases ← j.getObjValAs? (Array Json) "aliases"
  let functors ← j.getObjValAs? (Array Json) "functors"
  let some functor := functors.find? fun candidate =>
    (candidate.getObjValAs? String "id").toOption == some "fun.sets.identity"
    | throw "registered Sets identity functor is absent"
  let functorId ← functor.getObjValAs? String "id"
  if functorId != "fun.sets.identity" then
    throw s!"expected Sets identity functor, got {functorId}"
  let expression ← functor.getObjValAs? Json "expression"
  let expressionTag ← expression.getObjValAs? String "tag"
  if expressionTag != "identity" then
    throw s!"expected identity expression for Sets identity functor, got {expressionTag}"
  let names := cats.filterMap fun c => (c.getObjValAs? String "canonicalName").toOption
  for a in aliases do
    let spelling ← a.getObjValAs? String "spelling"
    if names.contains spelling then
      throw s!"alias spelling collides with category node: {spelling}"
  let families ← j.getObjValAs? (Array Json) "categoryFamilies"
  let some family := families.find? fun candidate =>
    (candidate.getObjValAs? String "id").toOption == some "fam.modules"
    | throw "registered Modules family is absent"
  let familyId ← family.getObjValAs? String "id"
  if familyId != "fam.modules" then
    throw s!"expected the Modules family, got {familyId}"
  let familySchema ← family.getObjValAs? String "schema"
  if familySchema != "ring" then
    throw s!"expected the Modules family schema to be ring, got {familySchema}"
  let parameters ← family.getObjValAs? (Array Json) "parameters"
  if parameters.size != 1 then
    throw s!"Modules family must have one parameter, got {parameters.size}"
  let some parameter := parameters[0]?
    | throw "registered Modules family has no parameter"
  let parameterKind ← parameter.getObjValAs? String "kind"
  if parameterKind != "parameter-kind.ring-object" then
    throw s!"Modules family parameter must be a RingCat object, got {parameterKind}"
  let variance ← family.getObjValAs? String "variance"
  if variance != "variance.restriction-of-scalars-contravariant" then
    throw s!"Modules family variance must be contravariant restriction of scalars, got {variance}"
  let transport ← family.getObjValAs? String "transport"
  if transport != "LeanCategories.Modules.Mathlib.moduleCatRestrictScalarsPseudofunctor" then
    throw s!"Modules family transport must be Mathlib's restriction-of-scalars pseudofunctor, got {transport}"
  pure ()

def run : IO UInt32 := do
  let manifest ← loadRegisteredManifest
  match Json.parse manifest.compress with
  | .error e =>
      IO.eprintln s!"JSON parse failed: {e}"
      return 1
  | .ok j =>
      match validate j with
      | .error e =>
          IO.eprintln e
          return 1
      | .ok () =>
          IO.println manifest.compress
          pure 0

def main : IO UInt32 :=
  run

end LeanCategories.Tools.ExportFull

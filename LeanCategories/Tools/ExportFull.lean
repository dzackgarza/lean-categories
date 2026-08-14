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
the private persistent extension `LeanCategories.registryExt` from
`LeanCategories.Catalogue.Registry.Extension`, then calls the checked manifest
path `LeanCategories.checkedRegistryManifest`.

Does **not** read external semantic-seed artifacts.
-/

open Lean Elab Command

namespace LeanCategories.Tools.ExportFull

open LeanCategories
open Tools

/-- Reload the compiled registry extension; this is the exporter data source. -/
def loadRegisteredManifestData : IO LeanCategories.RegistryManifest := do
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
  let result ← Lean.Core.CoreM.toIO LeanCategories.checkedRegistryManifestDTO
    { fileName := "", options := {}, fileMap := default } { env }
  pure result.1

def loadRegisteredManifest : IO Json := do
  return toJson (← loadRegisteredManifestData)

/-- Validate Lean-authored registry JSON. -/
def validate (expected : LeanCategories.RegistryManifest) (j : Json) : Except String Unit := do
  LeanCategories.Catalogue.Standard.validateStandardManifest expected
  let actual ← fromJson? j
  unless actual == expected do
    throw "exported registry manifest does not match the checked registry state"
  unless toJson actual == j do
    throw "exported registry manifest does not round-trip through its typed DTO"
  pure ()

def run : IO UInt32 := do
  let manifest ← loadRegisteredManifest
  let expected ← loadRegisteredManifestData
  match Json.parse manifest.compress with
  | .error e =>
      IO.eprintln s!"JSON parse failed: {e}"
      return 1
  | .ok j =>
      match validate expected j with
      | .error e =>
          IO.eprintln e
          return 1
      | .ok () =>
          IO.println manifest.compress
          pure 0

def main : IO UInt32 :=
  run

end LeanCategories.Tools.ExportFull

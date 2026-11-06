/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCategories.All
import LeanCategories.Catalogue
import LeanCategories.Tools.ReferenceGraph

/-!
# Emit the in-repository reference graph (#59)

Run with `lake env lean scripts/reference_graph.lean`, or `just reference-graph`.

Emission happens in a script elaborated with `lean`, not from a `run_cmd` inside the library build,
for a measured reason: the environment Lean *builds* a module in does not carry theorem bodies, so
there every theorem surfaces as `axiomInfo` and the graph reported 7,939 axioms in a library whose
axiom audit is green. `Lean.importModules` does the same. Only the environment of an ordinary
elaboration gives each theorem its `thmInfo` value.
-/

open Lean Elab Command

run_cmd do
  let rows := LeanCategories.Tools.ReferenceGraph.build (← getEnv)
  IO.FS.writeFile LeanCategories.Tools.ReferenceGraph.outputPath
    (LeanCategories.Tools.ReferenceGraph.toJson rows).compress
  let withRefs := rows.filter (fun r => r.refs.size > 0) |>.size
  logInfo m!"reference graph: {rows.size} declarations, {withRefs} with content references"

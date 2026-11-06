/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import LeanCategories.All

@[expose] public meta section

/-!
# The in-repository reference graph (#59)

For every `LeanCategories` declaration, the `LeanCategories` constants that occur in its type and
in its value. This is the sound basis for issue #59's card criterion — "a theorem is a card if
another module references it" — because it resolves names through the elaborated environment
rather than matching text. Text matching cannot distinguish a local lemma `map_snd` from
Mathlib's `Prod.map_snd`, and reports 571 cross-module theorems where the real figure is far
smaller.

The graph is emitted as JSON by the `lean-categories-reference-graph` executable, so the output
can be checked in beside the other audit artifacts and consumed by the extraction script.

Two exclusions, both structural rather than selective:

* the declaration itself, and the constructors/recursors generated beside it;
* `LeanCategories.Tools.*`, which is audit machinery and not mathematical content.
-/

open Lean Elab Command

namespace LeanCategories.Tools.ReferenceGraph

/-- Names that count as part of this repository's mathematical content. -/
def isContent (n : Name) : Bool :=
  (`LeanCategories).isPrefixOf n && !(`LeanCategories.Tools).isPrefixOf n

/-- The `LeanCategories` content constants occurring in an expression, deduplicated. -/
def contentConstants (e : Expr) : Array Name :=
  e.getUsedConstants.filter isContent

/-- The constants a declaration's type and value mention, excluding the declaration itself. -/
def references (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some info =>
    let ofValue := match info.value? with
      | some v => contentConstants v
      | none => #[]
    let all := contentConstants info.type ++ ofValue
    -- a declaration is not a reference to itself; private names are not content
    let all := all.filter fun c => c != n && !(`_private).isPrefixOf c
    all.qsort (·.toString < ·.toString)

/-- The declaration's kind, for the extraction script. -/
def kindOf (info : ConstantInfo) : String :=
  match info with
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | _ => "other"

/-- One row of the graph. -/
structure Row where
  name : Name
  kind : String
  module : Name
  /-- The `LeanCategories` constants referenced from the type or value. -/
  refs : Array Name
  /-- The `LeanCategories` constants referenced from the type only (the statement surface). -/
  typeRefs : Array Name
  deriving Inhabited

/-- The whole graph, sorted by declaration name. -/
def build (env : Environment) : Array Row := Id.run do
  let mut rows : Array Row := #[]
  for (n, info) in env.constants.toList do
    if !isContent n then continue
    match info with
    | .recInfo _ => continue        -- generated recursors duplicate their inductive
    | _ => pure ()
    let some mod := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[mod.toNat]!
    rows := rows.push
      { name := n, kind := kindOf info, module := modName
        refs := references env n
        typeRefs :=
          ((contentConstants info.type).filter (· != n)).qsort (·.toString < ·.toString) }
  return rows.qsort (·.name.toString < ·.name.toString)

/-- Serialize the graph. -/
def toJson (rows : Array Row) : Json :=
  Json.arr <| rows.map fun r =>
    Json.mkObj
      [ ("name", Json.str r.name.toString)
      , ("kind", Json.str r.kind)
      , ("module", Json.str r.module.toString)
      , ("refs", Json.arr (r.refs.map fun c => Json.str c.toString)) ]

/-- The reference graph of the current environment, as JSON text. -/
def json : CoreM String := do
  return (toJson (build (← getEnv))).pretty

/-- Where the emitted graph is checked in. -/
def outputPath : String := "LeanCategories/Tools/reference-graph.json"

-- Emit the graph at elaboration time, so the checked-in artifact cannot drift from the
-- environment it describes. Content is sorted, so an unchanged graph produces no diff.
run_cmd do
  let rows := LeanCategories.Tools.ReferenceGraph.build (← getEnv)
  let withRefs := rows.filter (fun r => r.refs.size > 0) |>.size
  IO.FS.writeFile LeanCategories.Tools.ReferenceGraph.outputPath
    (LeanCategories.Tools.ReferenceGraph.toJson rows).compress
  logInfo m!"reference graph: {rows.size} declarations, {withRefs} with content references"

end LeanCategories.Tools.ReferenceGraph

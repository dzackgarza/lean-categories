/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import CategoryGraph.All
public meta import CategoryGraph.Core.Linters

@[expose] public meta section

/-!
# Vacuous-witness audit

Drives `noBareNonempty` (defined in `CategoryGraph.Core.Linters`, imported
early so the rest of the library can carry `@[nolint noBareNonempty]`) as a
build-time gate over the whole environment, mirroring `AxiomAudit`'s `run_cmd`
pattern. It is also a real `Batteries.Tactic.Lint` linter — `#lint only
noBareNonempty` runs it interactively, `#list_linters` shows it.
-/

open Lean Elab Command Meta Batteries.Tactic.Lint CategoryGraph.Tools.VacuityAudit

namespace CategoryGraph.Tools.VacuityAudit

/-- Reject every exported `CategoryGraph` declaration carrying a bare `Nonempty` witness. -/
def audit : CommandElabM Unit := do
  let env ← getEnv
  let names := env.constants.toList.map Prod.fst |>.filter fun name =>
    (`CategoryGraph).isPrefixOf name
  let mut violations : Array (Name × MessageData) := #[]
  for name in names do
    if ← liftTermElabM (shouldBeLinted `noBareNonempty name) then
      if let some msg ← liftTermElabM (noBareNonempty.test name) then
        violations := violations.push (name, msg)
  unless violations.isEmpty do
    throwError m!"bare Nonempty witnesses: {violations.toList}"

run_cmd audit

end CategoryGraph.Tools.VacuityAudit

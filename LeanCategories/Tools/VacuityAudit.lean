/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import LeanCategories.All
public meta import LeanCategories.Tools.Linters

@[expose] public meta section

/-!
# Vacuous-witness audit

Drives `noBareNonempty` from `LeanCategories.Tools.Linters` as a build-time gate over the
whole environment. It is also a `Batteries.Tactic.Lint` linter. `#lint only
noBareNonempty` runs it interactively, and `#list_linters` shows it.
-/

open Lean Elab Command Meta Batteries.Tactic.Lint LeanCategories.Tools.VacuityAudit

namespace LeanCategories.Tools.VacuityAudit

/-- Reject every exported `LeanCategories` declaration carrying a bare `Nonempty` witness. -/
def audit : CommandElabM Unit := do
  let env ← getEnv
  let names := env.constants.toList.map Prod.fst |>.filter fun name =>
    (`LeanCategories).isPrefixOf name
  let mut violations : Array (Name × MessageData) := #[]
  for name in names do
    if ← liftTermElabM (shouldBeLinted `noBareNonempty name) then
      if let some msg ← liftTermElabM (noBareNonempty.test name) then
        violations := violations.push (name, msg)
  unless violations.isEmpty do
    throwError m!"bare Nonempty witnesses: {violations.toList}"

run_cmd audit

end LeanCategories.Tools.VacuityAudit

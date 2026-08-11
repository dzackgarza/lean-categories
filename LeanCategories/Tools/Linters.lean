/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Batteries.Tactic.Lint.Basic

@[expose] public meta section

/-!
# Repo-local linters

Linter definitions live here because the library imports this module before the audit.
`LeanCategories/Tools/VacuityAudit.lean` imports `LeanCategories.All` and runs these
checks over the complete environment.
-/

open Lean Meta Batteries.Tactic.Lint

namespace LeanCategories.Tools.VacuityAudit

/-- A linter banning `Nonempty` from the type of any `LeanCategories` declaration.
`Nonempty P` asserts mere existence of a term of `P`; wherever the design calls
for an actual 2-cell, functor, or classifying map, that mere existence cannot be
composed with or computed against, and it typechecks identically whether the
intended construction is real or degenerate. Issue #30's "`Nonempty (CatCommSq
…)` is banned" amendment records the one violation already caught by review.
This linter makes that rule mechanical. -/
@[env_linter] def noBareNonempty : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No LeanCategories declaration exposes a bare Nonempty witness."
  errorsFound := "DECLARATIONS EXPOSE A BARE NONEMPTY WITNESS INSTEAD OF CONSTRUCTED DATA."
  test declName := do
    unless (`LeanCategories).isPrefixOf declName do return none
    if ← isPrivateOrAutoDecl declName then return none
    let info ← getConstInfo declName
    if info matches .recInfo .. then return none
    let some culprit := info.type.find? (·.isAppOf ``Nonempty) | return none
    return m!"type contains `{culprit}` — replace it with constructed data."

end LeanCategories.Tools.VacuityAudit

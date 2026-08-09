/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Batteries.Tactic.Lint.Basic

@[expose] public meta section

/-!
# Repo-local linters

Linter *definitions* live here, imported early, so that any `CategoryGraph`
declaration can carry `@[nolint <name>]`.
`LeanCategories/CategoryGraph/Tools/VacuityAudit.lean`
imports `LeanCategories.CategoryGraph.All` (built last) to run these checks over the whole
environment as a build-time gate; that file cannot also define the linters
`@[nolint ...]` annotations elsewhere in the library need to reference, since
`nolint` requires the named linter to already be registered when it elaborates.
-/

open Lean Meta Batteries.Tactic.Lint

namespace CategoryGraph.Tools.VacuityAudit

/-- A linter banning `Nonempty` from the type of any `CategoryGraph` declaration.
`Nonempty P` asserts mere existence of a term of `P`; wherever the design calls
for an actual 2-cell, functor, or classifying map, that mere existence cannot be
composed with or computed against, and it typechecks identically whether the
intended construction is real or degenerate. Issue #30's "`Nonempty (CatCommSq
…)` is banned" amendment records the one violation already caught by review;
this linter makes the rule mechanical instead of a review norm recorded only in
issue prose. Exempt a specific declaration with `@[nolint noBareNonempty]` plus
a comment justifying why mere existence is actually intended there. -/
@[env_linter] def noBareNonempty : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No CategoryGraph declaration exposes a bare Nonempty witness."
  errorsFound := "DECLARATIONS EXPOSE A BARE NONEMPTY WITNESS INSTEAD OF CONSTRUCTED DATA."
  test declName := do
    unless (`CategoryGraph).isPrefixOf declName do return none
    if ← isPrivateOrAutoDecl declName then return none
    let info ← getConstInfo declName
    if info matches .recInfo .. then return none
    let some culprit := info.type.find? (·.isAppOf ``Nonempty) | return none
    return m!"type contains `{culprit}` — replace with a constructed witness, or \
      `@[nolint noBareNonempty]` with a comment justifying mere existence here."

end CategoryGraph.Tools.VacuityAudit

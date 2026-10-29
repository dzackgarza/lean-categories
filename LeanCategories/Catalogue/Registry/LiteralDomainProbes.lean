/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Default literal domains are unique registered object selectors

These are checks of the published metadata interface, not new mathematical
objects or acceptance assertions. A reader selects the registered object by
the syntax's domain selector instead of choosing a named scalar object itself.
Explicit ambient objects and the existing operations on them remain unchanged.
-/

namespace CasCatalogue

open Lean Meta in
run_meta do
  let state ← semanticState
  for (selector, declaration) in
      [("literal.integral.domain", ``Foundation.Objects.integers),
       ("literal.finite_subset.domain", ``Foundation.Objects.integers),
       ("literal.fractional.domain", ``Algebra.NamedRings.rationals)] do
    let rows := state.objects.filter (·.notations.contains selector)
    unless rows.size == 1 do
      throwError "literal domain selector {selector} must have exactly one owner"
    let some row := rows[0]? | throwError "missing literal domain selector {selector}"
    unless row.category == CategoryId.sets && row.declaration == declaration do
      throwError "literal domain selector {selector} changed its existing mathematical object"
    let probe := { row with id := ⟨"obj.probe.literal_domain"⟩, name := "probe literal domain" }
    validateObject state { probe with notations := #[] }
    let refusal ← try
      validateObject state { probe with notations := #[selector] }
      pure none
    catch e => pure (some (← e.toMessageData.toString))
    match refusal with
    | none => throwError "accepted a second owner of literal domain selector {selector}"
    | some message =>
        unless (message.splitOn "already selects an object").length > 1 do
          throwError "duplicate literal selector refused for another reason: {message}"

end CasCatalogue

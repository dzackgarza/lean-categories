/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
# Kernel-axiom audit — LeanCategories

Checks every exported `LeanCategories` declaration against the standard Lean
axiom budget, mirroring `LeanCategories/CategoryGraph/Tools/AxiomAudit.lean` exactly (same
mechanism, different name prefix). This is a separate sibling file, not an
extension of that file's own filter, for two reasons: that file backs the
existing `category-graph-axiom-audit` `lake_exe` and the external
`lean-axiom-audit` gate, which this repo's issue tracker (#30) already
consumes under that specific name/scope — widening its filter would silently
change what an already-relied-upon target checks. And `LeanCategories`
declarations that transitively call a raw `axiom` (the entire point of this
file) would otherwise never be checked at all: before this file, nothing in
this repo's automation looked at `LeanCategories`'s axiom footprint.

This is a kernel-assumption audit only; it does not establish that a Lean
statement has the intended mathematical meaning. It is a signal, not a gate:
a bare `axiom` for a classical theorem this project's own `#21` ledger says
should never live in the library root (`propext`/`Classical.choice`/`Quot.sound`
only, anything else is a conjecture, quarantined out of compilation) belongs
red until it is actually quarantined or proved — not `@[nolint]`-equivalent
special-cased away. There is no `@[nolint]`-style exemption mechanism here on
purpose: an axiom either belongs in `#21`'s quarantine (excluded from
compilation entirely, so this check never even sees it) or it doesn't belong
at all.
-/

open Lean Elab Command

namespace LeanCategories.Meta.AxiomAudit

/-- The standard Lean axioms permitted by the authoritative release policy. -/
def permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Reject exported LeanCategories declarations that use nonstandard assumptions. -/
def audit : CommandElabM Unit := do
  let env ← getEnv
  let names := env.constants.toList.map Prod.fst |>.filter fun name =>
    (`LeanCategories).isPrefixOf name
  let mut violations : Array (Name × Array Name) := #[]
  for name in names do
    let assumptions ← collectAxioms name
    let unexpected := assumptions.filter fun assumption => !permitted.contains assumption
    if !unexpected.isEmpty then
      violations := violations.push (name, unexpected.qsort Name.lt)
  if !violations.isEmpty then
    throwError m!"nonstandard axiom dependencies: {violations.toList}"

run_cmd audit

end LeanCategories.Meta.AxiomAudit

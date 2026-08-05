/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import CategoryGraph.All
public meta import Batteries.Tactic.Lint

@[expose] public meta section

/-!
# Standard Batteries/Mathlib linter audit — CategoryGraph

Runs Batteries' default `#lint` battery (`checkType`, `synTaut`,
`unusedHavesSuffices`, the `simpNF` family, Mathlib's naming and
`structureInType`/`deprecatedNoSince` additions, etc.) against every
`CategoryGraph` declaration, as a permanent signal, not a one-off recon.
`docBlame` is deliberately excluded: writing several hundred pre-existing
doc-strings is real but explicitly later work, not part of this pass.

`unusedArguments` is ALSO excluded here, but this is not a coverage gap:
Batteries' `unusedArguments` `#lint` check silently drops true findings at
this codebase's scale (confirmed reproducible via `lintCore` directly, via
`#lint` in batches of 5, and via a from-scratch `Task`-free reimplementation
of its exact check logic — root cause not identified). But the same class of
bug (unused function/theorem parameters) is already covered, reliably, by
Lean 4's own built-in `linter.unusedVariables` — a core-compiler linter, not
Mathlib/Batteries, that runs on every declaration as part of ordinary
elaboration and has none of the observed scale problems. See the `just
_lean-unused-variables` recipe in `justfile`, which gates on it directly.

`LeanCategories` gets its own sibling file (`LeanCategories/Meta/MathlibLintAudit.lean`)
rather than being added here, and each linter gets its own `#lint` command
rather than being batched: mixing packages or batching linters made the same
class of silent-drop worse, not better.

This is a signal, not a gate: it is expected to fail loudly on real findings
until they are actually fixed. Do not add `@[nolint]` here to make it pass —
that would silence exactly the thing this file exists to surface. `@[nolint]`
is for a finding that is inspected and genuinely correct as-is, never for
"this would take work to fix."
-/

-- The standard battery minus `docBlame` and `unusedArguments` (see module doc).
#lint only checkType in CategoryGraph
#lint only defsWithUnderscore in CategoryGraph
#lint only deprecatedNoSince in CategoryGraph
#lint only impossibleInstance in CategoryGraph
#lint only noBareNonempty in CategoryGraph
#lint only nonClassInstance in CategoryGraph
#lint only simpComm in CategoryGraph
#lint only simpNF in CategoryGraph
#lint only structureInType in CategoryGraph
#lint only subsetDotNotationLinter in CategoryGraph
#lint only synTaut in CategoryGraph
#lint only tacticDocs in CategoryGraph
#lint only unusedHavesSuffices in CategoryGraph

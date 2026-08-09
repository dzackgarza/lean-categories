/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import LeanCategories.All
public meta import Batteries.Tactic.Lint

@[expose] public meta section

/-!
# Standard Batteries/Mathlib linter audit — LeanCategories

Runs Batteries' default `#lint` battery (`checkType`, `synTaut`,
`unusedHavesSuffices`, the `simpNF` family, Mathlib's naming and
`structureInType`/`deprecatedNoSince` additions, etc.) against every
`LeanCategories` declaration, as a permanent signal, not a one-off recon.
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

Each linter gets its own `#lint` command. Batching linters made the same silent-drop
failure worse.

This audit fails loudly on real findings. Fix each finding in its declaration.
-/

-- The standard battery minus `docBlame` and `unusedArguments` (see module doc).
#lint only checkType in LeanCategories
#lint only defsWithUnderscore in LeanCategories
#lint only deprecatedNoSince in LeanCategories
#lint only impossibleInstance in LeanCategories
#lint only noBareNonempty in LeanCategories
#lint only nonClassInstance in LeanCategories
#lint only simpComm in LeanCategories
#lint only simpNF in LeanCategories
#lint only structureInType in LeanCategories
#lint only subsetDotNotationLinter in LeanCategories
#lint only synTaut in LeanCategories
#lint only tacticDocs in LeanCategories
#lint only unusedHavesSuffices in LeanCategories

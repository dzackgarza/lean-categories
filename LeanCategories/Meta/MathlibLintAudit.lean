/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import LeanCategories
public meta import Batteries.Tactic.Lint

@[expose] public meta section

/-!
# Standard Batteries/Mathlib linter audit — LeanCategories

Runs the same standard `#lint` battery as
`LeanCategories/CategoryGraph/Tools/MathlibLintAudit.lean`
(minus `docBlame` and `unusedArguments`) against every `LeanCategories`
declaration, as a permanent signal. See that file's module doc for why
`unusedArguments` is excluded here (not a coverage gap — Lean 4's own
built-in `linter.unusedVariables`, gated by `just _lean-unused-variables`,
covers unused parameters reliably instead) and why each linter gets its own
`#lint` command rather than being batched.

This is a signal, not a gate: it is expected to fail loudly on real findings
until they are actually fixed. Do not add `@[nolint]` here to make it pass —
that would silence exactly the thing this file exists to surface. `@[nolint]`
is for a finding that is inspected and genuinely correct as-is, never for
"this would take work to fix."
-/

-- The standard battery minus `docBlame` and `unusedArguments` (see module doc).
#lint only checkType in LeanCategories
#lint only defsWithUnderscore in LeanCategories
#lint only deprecatedNoSince in LeanCategories
#lint only impossibleInstance in LeanCategories
#lint only nonClassInstance in LeanCategories
#lint only simpComm in LeanCategories
#lint only simpNF in LeanCategories
#lint only structureInType in LeanCategories
#lint only subsetDotNotationLinter in LeanCategories
#lint only synTaut in LeanCategories
#lint only tacticDocs in LeanCategories
#lint only unusedHavesSuffices in LeanCategories

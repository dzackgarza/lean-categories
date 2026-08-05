# lean-categories — the shared Lean baseline of categorical constructions.
#
# Lake owns compilation and Mathlib supplies the dependency cache. Language-level
# QC law is delegated to the global gate (~/ai-review-ci/justfiles/lean.just);
# this file keeps only build entry points, the repo-supplied kernel-axiom audit,
# and the repo's additive convention layer.
#
# Not yet wired: the global lean-semgrep gate (Lean referent tripwires). It is
# adopted the moment the legacy tree's axiom/shim debt is burned down by work
# units #30–#40 — flipping it on earlier would red-gate main on known, owned
# debt. Do not add suppressions to adopt it sooner.

set dotenv-load := true

# Show available recipes
default:
    @just --list

# Build both libraries and the registry exporter
build:
    @lake build

# Fetch Mathlib's prebuilt compilation cache
cache:
    @lake update
    @lake exe cache get

# Run the complete repository quality gate
test: build
    @lake exe category-graph-export >/dev/null
    @just -f ~/ai-review-ci/justfiles/lean.just -d . lean-no-sorry
    @just _lint-conventions
    @just _lean-vacuity-audit
    @just _lean-mathlib-lint-audit
    @just _lean-unused-variables

[private]
test-commit: test

# Run the CI quality gate
test-ci: test

# Repo-supplied kernel-axiom audit, consumed by the global lean-axiom-audit gate
[private]
_lean-axiom-audit:
    @lake exe category-graph-axiom-audit

# Repo-supplied vacuous-witness audit (bans bare `Nonempty` in exported
# CategoryGraph types; see CategoryGraph/Tools/VacuityAudit.lean). No `lake
# exe` wrapper: the check is a `Batteries.Tactic.Lint` `env_linter`, which the
# attribute framework requires to be `meta`, and `meta` declarations cannot
# back a plain compiled executable. Building the module is enough — `run_cmd
# audit` inside it fires at elaboration time. Run directly in `test` rather
# than through the global gate, unlike axiom-audit, since no shared gate
# target for this check exists yet.
[private]
_lean-vacuity-audit:
    @lake build CategoryGraph.Tools.VacuityAudit

# Repo-supplied standard Batteries/Mathlib `#lint` battery, minus `docBlame`
# (later work, see the files' module docs) and `unusedArguments` (demonstrated
# unreliable at this codebase's scale via Batteries' `#lint`/`lintCore` and via
# a from-scratch reimplementation of its exact check; both silently dropped a
# known-true finding under load with no crash or exception, root cause not
# identified — see CategoryGraph/Tools/MathlibLintAudit.lean's module doc).
# Unused-argument checking is NOT actually missing, though: `_lean-unused-variables`
# below covers it via a different, already-reliable mechanism. This is a
# signal, not a gate: it is meant to fail loudly on real findings and stay red
# until they are fixed, not be forced green by `@[nolint]`-ing anything
# inconvenient.
[private]
_lean-mathlib-lint-audit:
    @lake build CategoryGraph.Tools.MathlibLintAudit LeanCategories.Meta.MathlibLintAudit

# Gates on Lean 4's own built-in `linter.unusedVariables` (core compiler, not
# Mathlib/Batteries) — covers unused function/theorem parameters
# (`linter.unusedVariables.funArgs`, on by default) with none of the
# reliability problems `_lean-mathlib-lint-audit`'s `unusedArguments` hit: it
# runs as part of ordinary elaboration on every declaration, always has, and
# `lake build` reliably replays every cached warning on every invocation (even
# fully cached, doing no recompilation) rather than only surfacing them once.
# Reuses the `build` step's cache; grep, not a rebuild.
[private]
_lean-unused-variables:
    #!/usr/bin/env bash
    set -euo pipefail
    matches="$(lake build 2>&1 | grep -B2 'linter.unusedVariables' || true)"
    if [ -n "$matches" ]; then
        echo "$matches"
        echo 'ERROR: unused-variable/parameter warnings present (Lean core linter.unusedVariables).' >&2
        exit 1
    fi

# Additive local convention layer (project rulings; see issue #1 and AGENTS.md).
# Cartan matrices have no role in this program's lattice conventions: Gram
# matrices are defined by cited root presentations (Corrections 2–3 on #1).
[private]
_lint-conventions:
    #!/usr/bin/env bash
    set -euo pipefail
    matches="$(rg -n --glob '*.lean' 'Cartan' . || true)"
    if [ -n "$matches" ]; then
        echo "$matches"
        echo 'ERROR: Cartan matrices are banned from lattice conventions (issue #1, Correction 3).' >&2
        exit 1
    fi

[private]
test-push: test-ci
    @just -f ~/ai-review-ci/justfiles/lean.just -d . lean-axiom-audit

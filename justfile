# lean-categories — the shared Lean baseline of categorical constructions.
#
# Lake owns compilation and Mathlib supplies the dependency cache. Language-level
# QC law is delegated to the global ai-review-ci checkout;
# this file keeps build entry points and repo-supplied Lean audits.
#
# Not yet wired: the global lean-semgrep gate (Lean referent tripwires). It is
# adopted the moment the legacy tree's axiom/shim debt is burned down by work
# units #30–#40 — flipping it on earlier would red-gate main on known, owned
# debt. Do not add suppressions to adopt it sooner.

set dotenv-load := true

ai_review_ci := env_var("HOME") / "ai-review-ci"

# Show available recipes
default:
    @just --list

# Move this worktree to the Mathlib master head without decompressing its build
# tree here. Mathlib's own lakefile fetches the cache at the end of `lake update`
# (lakefile.lean:193-197, the `post_update` hook) and writes it into this
# worktree's tree -- that hook is what put four copies of Mathlib on the VM's
# disk, because it runs before scripts/cache-get.sh can hand out the one shared
# tree. MATHLIB_NO_CACHE_ON_UPDATE=1 turns it off, so the cache step below runs
# instead, once per revision for every worktree. Use `just update`, not a bare
# `lake update`, then `just cache` (or `just build`, which runs the cache step).
update:
    @MATHLIB_NO_CACHE_ON_UPDATE=1 lake update

# Build the library on Mathlib's prebuilt cache (machine-wide in ~/.cache/mathlib).
# scripts/cache-get.sh gives this worktree a tree of hardlinks into the one Mathlib
# build the repository keeps per Mathlib revision (see docs/mathlib-build-store.md),
# so four worktrees cost one copy of it, and a head move still cannot leave stale
# traces hiding the gap behind a fresh `lake build`.
build:
    @scripts/cache-get.sh
    @lake build

# Fetch Mathlib's prebuilt compilation cache (linking this worktree to the shared tree)
cache:
    @scripts/cache-get.sh

# Run the complete repository quality gate
test: build
    @just -f {{ai_review_ci}}/justfiles/lean.just -d . lean-no-sorry
    @just _lean-vacuity-audit
    @just _lean-mathlib-lint-audit
    @just _lean-unused-variables
    @just _lean-axiom-audit

# Commit- and push-tier QC is non-elaborating, so a worker can bank a partially
# elaborated transcription. Full elaboration, exporter/linter/axiom audits run in CI
# (`test-ci`), where `test` remains the complete repository gate.
test-commit:

# Run the CI quality gate
test-ci: test

# Emit the in-repository reference graph to LeanCategories/Tools/reference-graph.json (#59).
reference-graph:
    @lake env lean scripts/reference_graph.lean

# Emit LeanCategories modules as Prove2Me definition payloads (#59).
#   just publish-prove2me --dry-run          # write payloads, no network
#   just publish-prove2me --layer 0          # one import layer
#   just publish-prove2me --private          # stage privately on the platform
publish-prove2me *ARGS:
    @python3 scripts/publish_prove2me.py {{ARGS}}

# Regenerate the derived foundational-corpus scheduling frontier. The canonical
# whole-source status ledger remains the sole sweep-completion authority.
foundational-frontier:
    @python3 scripts/foundational_frontier.py > FOUNDATIONAL_FRONTIER.md

# Repo-supplied kernel-axiom audit, consumed by the global lean-axiom-audit gate
[private]
_lean-axiom-audit:
    @lake exe lean-categories-axiom-audit

# Repo-supplied vacuous-witness audit (bans bare `Nonempty` in exported
# LeanCategories types; see LeanCategories/Tools/VacuityAudit.lean). No `lake
# exe` wrapper: the check is a `Batteries.Tactic.Lint` `env_linter`, which the
# attribute framework requires to be `meta`, and `meta` declarations cannot
# back a plain compiled executable. Building the module is enough — `run_cmd
# audit` inside it fires at elaboration time. Run directly in `test` rather
# than through the global gate, unlike axiom-audit, since no shared gate
# target for this check exists yet.
[private]
_lean-vacuity-audit:
    @lake build LeanCategories.Tools.VacuityAudit

# Repo-supplied standard Batteries/Mathlib `#lint` battery, minus `docBlame`
# (later work, see the files' module docs) and `unusedArguments` (demonstrated
# unreliable at this codebase's scale via Batteries' `#lint`/`lintCore` and via
# a from-scratch reimplementation of its exact check; both silently dropped a
# known-true finding under load with no crash or exception, root cause not
# identified — see LeanCategories/Tools/MathlibLintAudit.lean's module doc).
# Unused-argument checking is NOT actually missing, though: `_lean-unused-variables`
# below covers it via a different, already-reliable mechanism. This is a
# signal, not a gate: it is meant to fail loudly on real findings and stay red
# until they are fixed, not be forced green by `@[nolint]`-ing anything
# inconvenient.
[private]
_lean-mathlib-lint-audit:
    @lake build LeanCategories.Tools.MathlibLintAudit

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

[private]
test-push:
    @just -f {{ai_review_ci}}/justfiles/lean.just -d . lean-no-sorry

# Regenerate the corpus site pages from the agent-memory vault
site-build:
    @python3 site/build.py

# Serve the corpus site locally with live reload
site-preview: site-build
    @uvx --from quarto-cli quarto preview site --port 7655

# Render the corpus site to site/_site, as CI does
site-render: site-build
    @uvx --from quarto-cli quarto render site --output-dir _site

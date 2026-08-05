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

[private]
test-commit: test

# Run the CI quality gate
test-ci: test

# Repo-supplied kernel-axiom audit, consumed by the global lean-axiom-audit gate
[private]
_lean-axiom-audit:
    @lake exe category-graph-axiom-audit

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

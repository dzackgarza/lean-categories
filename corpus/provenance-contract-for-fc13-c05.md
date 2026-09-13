---
type: reference
title: Provenance contract for FC13 C05
description: '# Provenance contract for FC13 C05'
tags:
- project
- reference
timestamp: '2026-09-07T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# Provenance contract for FC13 C05

# Provenance contract for FC13 C05

## Provenance contract for FC13 C05

- Canonical source block: FC13 Matsumura Chapter 5, `FC13-C05-U001`–`FC13-C05-U066`, §§13–15 and the appendix to §13, in canonical source-ID order from [[foundational-corpus-units-fc13-matsumura]]. The generator retrieves the promoted catalogue through `agent-memory`, asserts all 66 IDs occur once and in order, and emits one route per source unit.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280` (Lean 4.33.0, Apache-2.0). `LeanCategories/Algebra/DimensionTheory.lean` owns `PoincareSeries`, `HilbertFunction`, `IsSystemOfParameters`, and `AffineVarietyDimension`. Only U009 is wholly owned by that interface; U028 includes a module-level parameter definition absent from the project, so it is not classified project-existing.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Apache-2.0, Lean 4.33.0. Every native path/token is validated against that exact checkout. Native C05 coverage is concentrated in graded-ring/homogeneous-submodule infrastructure, Krull height, regular-local embedding dimension, fibre rings, and the height/fibre inequality with going-down equality.
- Current Mathlib was refreshed 2026-09-07 to `H=e281a66114fe17935e6ea7917a01b714d0c1e493` (Lean 4.34.0-rc2). The associated-graded work remains open in PRs #33218–#33220 and is definition-level only for the source bundles here. Mathlib PR #9819, head `413e5b872a7c758e0eb91f99cb96d6a61c81f0a2`, is an older Apache-2.0 branch on Lean 4.9.0-rc3 that contains the graded Hilbert-basis, finite-piece, Hilbert–Serre and Hilbert-polynomial results. Those four exact semantic owners are recorded as `reference-port`, not importable package routes.
- Search channels used project source, P, current/open Mathlib, Mathlib source/docs, Loogle/LeanSearch-oriented repository tooling, Reservoir/indexed discovery, and GitHub-wide Lean-code search. Targeted searches for Hilbert–Samuel, systems of parameters, analytic independence, catenarity, and dimension formula found no complete compatible owner beyond the project/PRs already recorded.
- Strict bundle semantics were enforced. U003/U004 are not credited from homogeneous/weighted polynomial APIs because pinned quotient grading is missing; U005/U006/U014 are not credited from associated-graded definitions without completion/generation/finiteness theorems; U028 is not credited from the project ring-only parameter predicate; U056 is not credited from polynomial dimension without the formal-power-series equality; and U063–U066 are not credited from `ReesAlgebra` without the associated-graded/deformation/dimension clauses.
- Hilbert polynomial and Hilbert–Samuel polynomial are kept distinct. PR #9819 supplies the former for graded modules (U010–U011) but not the Samuel function, d(M), multiplicity, reductions, or the §14 formulas. U015–U018 and U039–U051 therefore remain unmatched rather than being mapped through a superficially similar polynomial API.
- Route totals for C05: `mathlib` 6, `project-existing` 1, `package-import` 0, `reference-port` 4, `unmatched` 55.

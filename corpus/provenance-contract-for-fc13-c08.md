---
type: reference
title: Provenance contract for FC13 C08
description: '# Provenance contract for FC13 C08'
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
# Provenance contract for FC13 C08

# Provenance contract for FC13 C08

## Provenance contract for FC13 C08

- Canonical source block: FC13 Matsumura Chapter 8, `FC13-C08-U001`–`FC13-C08-U043`, §§22–24, in canonical source-ID order from [[foundational-corpus-units-fc13-matsumura]]. The generator retrieves all 43 units through `agent-memory`, asserts exact order/uniqueness, and assigns one route per unit.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280` (Lean 4.33.0, Apache-2.0). No project-owned API covers a whole C08 source unit beyond the upstream primitives, so C08 has no `project-existing` route.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0. Two source units have complete native assemblies: U006 via height additivity + flat going down + fibre localization, and U036 via Noetherian finite type⇒finite presentation + flat going down + Chevalley openness.
- Current Mathlib was refreshed 2026-09-07 to `H=e281a66114fe17935e6ea7917a01b714d0c1e493` (Lean 4.34.0-rc2). Open-PR searches for Serre conditions, miracle flatness, generic freeness and flat loci were negative. The CM/Gorenstein PR stack from FC13 C06 was searched for flat/base-change/fibre theorems; no exact C08 flat-family owner was found.
- Search channels used project source, P, H/current/open Mathlib, source/docs, Loogle/LeanSearch-oriented repository tooling, Reservoir/indexed discovery, and GitHub-wide Lean-code search. Literal searches for “ideal-separated”, “miracle flatness”, “Serre condition”, and source-shaped generic freeness produced no compatible owner.
- Strict bundle semantics were enforced. U005 is not credited from generic associated-graded definitions; U012–U029 are not inferred from separate CM/Gorenstein/flat definitions; U030 is not credited from a derivable tensor/quotient comparison without an exported fibre equivalence; U035 is not replaced by the free locus; and the Nagata-criterion rows U034/U038–U043 are kept distinct from generic topology/local-property machinery.
- Route totals for C08: `mathlib` 2, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 41.

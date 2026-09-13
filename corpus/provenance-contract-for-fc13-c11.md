---
type: reference
title: Provenance contract for FC13 C11
description: '# Provenance contract for FC13 C11'
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
# Provenance contract for FC13 C11

# Provenance contract for FC13 C11

## Provenance contract for FC13 C11

- Canonical source block: FC13 Matsumura Chapter 11, `FC13-C11-U001`–`FC13-C11-U051`, §§31–33, in canonical source-ID order from [[foundational-corpus-units-fc13-matsumura]]. All 51 IDs are retrieved through `agent-memory`, asserted once/in-order, and assigned exactly one route.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280`. No project-owned catenary, G-ring/excellence, Nagata-ring, or normalization theorem closes a C11 unit more completely than pinned Mathlib.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0. Native C11 coverage is concentrated in the normalization tail: `integralClosure A (FractionRing A)`, `IsIntegralClosure.finite` for finite separable extensions, and Noether normalization.
- Current Mathlib was refreshed 2026-09-07 to `H=e281a66114fe17935e6ea7917a01b714d0c1e493`. Targeted P/H/open searches found no catenary/equidimensional/formally-catenary predicates, G-ring/excellence/Nagata-ring interfaces, geometrically-regular regular homomorphisms, or general Krull-ring/Mori–Nagata development.
- Strict bundle semantics were enforced. `Ideal.Fiber` plus completion does not by itself create a formal-fibre interface; smooth maps are not substituted for EGA regular homomorphisms; and U043 is not credited from the separable normalization theorem because the source explicitly includes the purely inseparable case.
- No compatible open PR supplied a complete additional C11 row.
- Route totals for C11: `mathlib` 3, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 48.

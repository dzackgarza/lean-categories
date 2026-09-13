---
type: reference
title: Provenance contract for FC13 C00
description: '# Provenance contract for FC13 C00'
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
# Provenance contract for FC13 C00

# Provenance contract for FC13 C00

## Provenance contract for FC13 C00

- Canonical source block: FC13 Matsumura front matter, `FC13-C00-U001`–`FC13-C00-U005`, in canonical source-ID order from [[foundational-corpus-units-fc13-matsumura]]. All five catalogue rows are mapped exactly once; no FC01–FC07 mapping record and no Sweep-I catalogue was modified.
- Project-first inspection was performed at repository HEAD `A=3b2239e161592472b34e02ad3b7da308f9ce7280` on Lean 4.33.0. `LeanCategories/Algebra/Ideals.lean` (Apache-2.0 file header) already owns the complete U002 interface: `idealMapOrderHom` / `idealComapOrderHom` are definitionally `Ideal.map` / `Ideal.comap`, with object theorems exposing the maps. This is therefore `project-existing` rather than a redundant Mathlib route.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Apache-2.0, Lean 4.33.0 and directly project-compatible. Every Mathlib path and declaration promoted in C00 was inspected at that exact revision. The generator validation checks each cited path against the pinned checkout and checks the cited declaration token in that file.
- Current Mathlib was refreshed on 2026-09-07 to `H=f15b4f161f6ff698ab91b4494faa75925856d0f5`, Apache-2.0, Lean 4.34.0-rc2. The C00 primitives `CommRing`, `RingHom`, `Subring`, `Ideal.span`, `StrictMono`, `CharP`, and `Nat.Prime` remain present with the same relevant interfaces; no C00 route depends on post-pin code.
- Open Mathlib PR searches on 2026-09-07 for `CommRing`, `Ideal.map`, `Ideal.span`, `StrictMono`, and `CharP` found only downstream instances, corollaries, tactics, or applications relevant to these names; none supplied a distinct C00 interface that supersedes the project/P route.
- Loogle and LeanSearch were queried through the pinned project’s `LeanSearchClient`; current Mathlib documentation, Lean Reservoir, and indexed GitHub Lean repositories were also searched for the C00 notions. External hits were downstream users/extensions of the Mathlib primitives, not independently owned replacements. Consequently C00 has no `package-import` or `reference-port` route.
- Strict bundle semantics govern each row. U001 is credited only as the bundle `CommRing` + unital `RingHom` + `Subring`, because no one component alone states all three source conventions. U003 uses `Ideal.span` together with `span_insert`, which gives the finite sum of principal ideals by iteration. U004 records both non-strict inclusion and a genuinely strict indexed chain. U005 deliberately uses `CharP R p` together with `Nat.Prime p`; `CharP` alone does not imply that an arbitrary characteristic is prime.
- Route totals for C00: `mathlib` 4, `project-existing` 1, `package-import` 0, `reference-port` 0, `unmatched` 0.


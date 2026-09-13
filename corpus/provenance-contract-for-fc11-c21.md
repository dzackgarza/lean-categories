---
type: reference
title: "Provenance contract for FC11 C21"
description: "# Provenance contract for FC11 C21"
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
# Provenance contract for FC11 C21

## Provenance contract for FC11 C21

- Canonical source block: FC11 Peters–Sterk Chapter 21, “Enriques Surfaces”, `FC11-C21-U001`–`FC11-C21-U038`, 38 units, exact canonical order from [[foundational-corpus-units-fc11-peters-sterk]].
- Project baseline `A=12618f8abc2b4852b3da9ab65c3bc547ac4c1f19` (Apache-2.0, Lean 4.33.0); pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0); current upstream Mathlib `H=71a80585ee495fc24472fd0eaffc89d94e4fd8d6`.
- LeanSearch unit queries were attempted for all remaining FC11 rows; the service began returning HTTP 429 during C04, so rate-limit failures were not used as negative evidence. Project and pinned/current Mathlib were searched locally by source family; the source atlas, package/Reservoir families, Loogle/LeanSearch where available, broad GitHub Lean search, and known reference corpora were also checked.
- Unit-level LeanSearch captures: 0/38 successful, 38 service errors.
- 2026-09-13 `remap-strict-bundle` rule: source units are matched clause by clause; a row may assemble several checked declarations when that conjunction realizes the source statement. `unmatched` is retained only for the residual source clauses after the checked Mathlib/project/reference/search evidence recorded in the mapping row; `project-existing` is accepted only with an explicit route to mapped source units, Mathlib primitives, or a cited reference implementation.
- TauCeti candidates, when used, are pinned at `98a6bfc9f3cb4ab3a159d83858ce546d1e543c1b` (Apache-2.0, Lean 4.34.0-rc2, Mathlib `e21ec05048292b3de86d4cf1987e2208171a5642`) and therefore route as `reference-port`, not direct package import, unless an independently compatible package owner is recorded.
- HassePrinciple candidates, when used, are pinned at `47df8f51939b364e678893d54e8a3faf6ec52302` (Apache-2.0, Lean 4.34.0-rc2, Mathlib `2fbace17aa59d5dd7d99fc4af3849722f69272df`) and likewise route as `reference-port`; declarations whose proof or required dependency remains `sorry` are not accepted as positive evidence.
- Route totals after the 2026-09-13 exact-route remap: `mathlib` 2, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 36; total 38.
- Negative-result scope is the dated 2026-09-13 remap evidence in each current `unmatched` row. Search-service errors, rate limits, and timeouts are not negative evidence; only inspected revisions and successful search surfaces cited by the row support its residual gap.

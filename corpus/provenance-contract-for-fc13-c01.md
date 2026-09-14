---
type: reference
title: Provenance contract for FC13 C01
description: '# Provenance contract for FC13 C01'
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
# Provenance contract for FC13 C01

# Provenance contract for FC13 C01

## Provenance contract for FC13 C01

- Canonical source block: FC13 Matsumura Chapter 1, `FC13-C01-U001`–`FC13-C01-U065`, §§1–3, in canonical source-ID order from [[foundational-corpus-units-fc13-matsumura]]. The generator retrieves that promoted catalogue through `agent-memory`, asserts all 65 IDs occur exactly once and in order, and emits exactly one Sweep-II route per unit.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280` on Lean 4.33.0. Project files are Apache-2.0. Exact project-owned complete interfaces were found for U026 (`LeanCategories/Algebra/Concrete/Rings.lean::UniqueFactorizationDomainCat`) and U033 (`LeanCategories/Modules/Mathlib.lean::FinitelyGeneratedModuleCat`). Project wrappers that cover only one clause of a larger source bundle were not used to reclassify Mathlib theorem bundles as `project-existing`.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, repository `leanprover-community/mathlib4`, Apache-2.0, Lean 4.33.0, and is directly compatible with the project. The generator verifies that the local Mathlib checkout is exactly P and that every cited pinned path and declaration token exists at P before producing the chapter record.
- Current Mathlib was independently refreshed on 2026-09-07 to `H=f15b4f161f6ff698ab91b4494faa75925856d0f5`, repository `leanprover-community/mathlib4`, Apache-2.0, Lean 4.34.0-rc2. Current-source inspection and open-PR searches were used especially for every pinned gap; no C01 unit receives `reference-port` because no exact post-pin declaration was found that closes a source bundle.
- Search channels: project source; pinned P; current H; open Mathlib PRs; Loogle and LeanSearch through the pinned project’s LeanSearchClient; Mathlib documentation/source; Lean Reservoir/indexed web results; and discoverable Lean repositories via GitHub code search. External results produced no compatible exact C01 package/import or reference-port route, so C01 has no `package-import` route.
- Strict bundle semantics were enforced. In particular: U022 is not credited from the unit/constant-term theorem plus one-variable maximal-ideal results because the source unit is finite-multivariable; U024 is not credited from a PID-only maximal-principal theorem; U041 is not credited from finite local projective-freeness; U048 is not credited from other local length formulas; U063 is not credited merely because the theorem is derivable from lower-level annihilator/Noetherian infrastructure; and U065 is not confused with finite-type Noetherian ascent, which is the opposite direction from Eakin–Nagata.
- U040 was checked specially against its exact arbitrary-commutative-ring hypotheses. The valid pinned route is `OrzechProperty.bijective_of_surjective_endomorphism` together with the commutative-ring `OrzechProperty` instance, not the more restrictive Noetherian Hopficity theorem.
- Route totals for C01 after the 2026-09-14 Mapping repair: `mathlib` 52, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 13. U023/U024 are now clause-wise Mathlib routes for their definitional/construction content; attached finite-generation/maximal-principal result clauses remain theorem work.


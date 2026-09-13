---
type: reference
title: Provenance contract for FC13 C04
description: '# Provenance contract for FC13 C04'
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
# Provenance contract for FC13 C04

# Provenance contract for FC13 C04

## Provenance contract for FC13 C04

- Canonical source block: FC13 Matsumura Chapter 4, `FC13-C04-U001`–`FC13-C04-U047`, §§10–12, in canonical source-ID order from [[foundational-corpus-units-fc13-matsumura]]. The generator retrieves the promoted catalogue through `agent-memory`, asserts all 47 IDs occur once and in order, and emits one route per unit.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280` (Lean 4.33.0, Apache-2.0). The project has category wrappers `ValuationRingCat`, `DiscreteValuationRingCat`, and `DedekindDomainCat`, plus fractional-ideal convenience definitions, but these are wrappers around pinned Mathlib and do not own a complete C04 row more fully than P. No row is classified `project-existing` from a wrapper alone.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Apache-2.0, Lean 4.33.0. Every promoted `mathlib` path/token is validated against that exact checkout. Relevant native areas are valuation subrings/local-subring domination, intrinsic value groups, DVR TFAEs and adic valuations, fractional ideals, and Dedekind ideal factorization.
- Current Mathlib was refreshed 2026-09-07 to `H=e281a66114fe17935e6ea7917a01b714d0c1e493`, Apache-2.0, Lean 4.34.0-rc2. Current/open searches found no post-pin Krull-ring development closing any §12 unit, and no Krull-Akizuki theorem or Zariski-Riemann valuation-space topology.
- Search channels used project source, P, H/current/open Mathlib, Mathlib docs/source, Loogle/LeanSearch-oriented repository tooling, Reservoir/indexed discovery, and GitHub-wide Lean-code search. The only concrete external Krull-domain hit was `acmepjz/lean-iwasawa@7fffeb8c80fbe13f989f318c23cbb0dcf2230092`; its relevant `IsKrullDomain` theorem development contains explicit `sorry`s and its predicate uses the canonical height-one localization family rather than Matsumura’s general defining-family object, so it is not a valid `reference-port` or package route.
- Strict bundle semantics were enforced. U002 is not credited from the prime/coarsening correspondence without the quotient/composite clauses; U014–U015 are not credited from Mathlib’s multiples-based `Archimedean` predicate without a checked Hölder embedding theorem; U026–U029 remain unmatched when only constituent projective/localization/height facts exist; and U035 is promoted only because both the integral-closure Dedekind theorem and finiteness of primes over a maximal ideal are explicit at P.
- Matsumura’s DVR definition (U019) is value-group based. P defines `IsDiscreteValuationRing` by the equivalent local-PID/nonfield condition and proves the associated valuation has value group ℤ, but no checked converse starts from the source value-group definition. U019 is therefore deliberately unmatched, while U020/U021/U024 use the exact pinned DVR valuation and equivalence theorems under their stated hypotheses.
- §12 U036–U047 is kept separate from Dedekind/height-one infrastructure: without a completed compatible Krull-ring object, generic DVR localization and factorization results are adjacent evidence only, not source-unit matches.
- Route totals for C04: `mathlib` 17, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 30.

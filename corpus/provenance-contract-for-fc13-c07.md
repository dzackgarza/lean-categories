---
type: reference
title: Provenance contract for FC13 C07
description: '# Provenance contract for FC13 C07'
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
# Provenance contract for FC13 C07

# Provenance contract for FC13 C07

## Provenance contract for FC13 C07

- Canonical source block: FC13 Matsumura Chapter 7, `FC13-C07-U001`–`FC13-C07-U055`, §§19–21, in canonical source-ID order from [[foundational-corpus-units-fc13-matsumura]]. All 55 IDs are retrieved through `agent-memory`, validated once/in-order, and assigned one route each.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280`. The project defines `LeanCategories.Homological.globalDimension`, but U006 bundles additional finite-module and local residue-field theorems not owned by the project, so the definition alone does not earn a `project-existing` route.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0. Native C07 owners include `IsRegularRing`, the Noetherian height-one-principal UFD criterion, GCD/lcm infrastructure, Picard modules/groups, and the invertible-fractional-ideal class group with `ClassGroup.equivPic`.
- Current Mathlib was refreshed 2026-09-07 to `H=e281a66114fe17935e6ea7917a01b714d0c1e493`. Exact open-branch owners are recorded as `reference-port`: PR #26215 (`fbbf6add2600af0c6046b367cd16729dc6e94e61`) Auslander–Buchsbaum; PR #29802 (`9c971a554fb6265f06b80bc62c7b314f4f2d33ec`) global dimension/Auslander–Buchsbaum–Serre/localization; PR #39510 (`a277a2ff8ecab34f00ad3e962eb7cbd18a35de02`) regular local UFD (inspected without `sorry`/`admit`); PR #34913 (`c7780ed427bbed31ee0c430a5594ed5ea4c7d5b5`) Koszul/complete-intersection ε₁ theory; and PR #41103 (`cb5e638c184221996aa2100f6cbb7074a55795bb`) CI⇒Gorenstein and the implication chain. These are ports, not importable package routes.
- Search channels used project source, P, H/current/open Mathlib, source/docs, Loogle/LeanSearch-oriented repository tooling, Reservoir/indexed discovery, and GitHub-wide Lean-code search. No compatible André–Quillen/cotangent-complex homology owner was found.
- Strict bundle semantics were enforced. U006 is not credited from a global-dimension definition plus regular-local residue-field theorem because the source local equality is arbitrary Noetherian local; U010/U011 remain unmatched despite derivable/local partial results; U024 is not credited from rank alone without the rank-one torsion-free-to-ideal theorem; and U037/U040–U045 are not mapped through pinned `ClassGroup`, because Matsumura uses the Weil divisor class group of a general Krull ring whereas P’s class group is invertible fractional ideals modulo principal ideals.
- PR #34913’s Koszul development was also used to correct FC13 C06 provenance before C07 promotion. In C07 it exactly supplies U003 and the ε₁/complete-intersection rows U047–U050; it still does not provide the higher ε_i family U046.
- Route totals for C07: `mathlib` 7, `project-existing` 0, `package-import` 0, `reference-port` 12, `unmatched` 36.

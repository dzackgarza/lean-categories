---
type: reference
title: Provenance contract for FC13 C06
description: '# Provenance contract for FC13 C06'
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
# Provenance contract for FC13 C06

# Provenance contract for FC13 C06

## Provenance contract for FC13 C06

- Canonical source block: FC13 Matsumura Chapter 6, `FC13-C06-U001`–`FC13-C06-U062`, §§16–18, in canonical source-ID order from [[foundational-corpus-units-fc13-matsumura]]. The generator retrieves the promoted catalogue through `agent-memory`, verifies all 62 IDs and emits exactly one route per unit.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280` (Lean 4.33.0, Apache-2.0). No project-owned wrapper covers a complete C06 unit beyond pinned Mathlib/open upstream developments, so C06 has no `project-existing` route.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Apache-2.0, Lean 4.33.0. Native coverage includes `Sequence.IsRegular`, the pinned Rees Ext/regular-sequence TFAE, and localization of injective modules. P explicitly lists Koszul and quasi-regular sequence theory as TODOs in `RegularSequence.lean`; those gaps are not papered over by generic homological-complex APIs.
- Current Mathlib was refreshed 2026-09-07 to `H=e281a66114fe17935e6ea7917a01b714d0c1e493` (Lean 4.34.0-rc2). The major exact post-pin owners are still open PRs: #26218 (`2a84ea75981e352045999fd11bc7ef6b8fab549f`) for depth/Ischebeck/CM definitions and localization; #26245 (`22bda9222808563de469a721b6f306abe18ebde5`) for CM height/depth/catenary formulas; #26957 (`cb58875d409523d7f9fe40519e8aec70c59855a4`) for unmixedness; #28599 (`fb96036190226357c7ee4450b46e9419df085bc5`) for polynomial CM; and the Gorenstein stack #31884/#32035/#41102 for definitions, localization and completion. These are `reference-port` routes, not package imports.
- Search channels used project source, P, current/open Mathlib, Mathlib source/docs, Loogle/LeanSearch-oriented repository tooling, Reservoir/indexed discovery, and GitHub-wide Lean-code search. Targeted searches for Koszul, quasi-regular sequences, CM completion/power series, injective hulls, Matlis duality, Bass numbers, and big CM found no complete compatible owner beyond the specific PRs recorded. PR #34913 (`c7780ed427bbed31ee0c430a5594ed5ea4c7d5b5`) supplies a substantial ring-valued Koszul complex, append exact sequence, annihilator homotopy, and regular-sequence acyclicity, but not Matsumura's arbitrary coefficient-module/general-complex/converse bundles U010–U014.
- Strict bundle semantics were enforced. U008 is not credited from the narrower pinned permutation theorem without Matsumura’s quasi-regular/separated bridge; U021 is not credited from constituent depth/height/projective-dimension facts without the full grade relation bundle; U028 is not credited from regular-sequence height criteria without the parameter-system theorem; U044 is not credited from Gorenstein definitions and Ext lemmas without the full eight-way Theorem 18.1 equivalence; and Matlis/Bass rows U050–U059 remain unmatched without an injective-hull framework.
- Gorenstein terminology is routed only after the source Theorem 18.1 row: PR #31884 selects finite self-injective dimension as the standard equivalent definition, PR #32035 proves prime-local stability, and PR #41102 proves completion invariance. The large source equivalence U044 itself remains unmatched because the open stack does not package all irreducible-parameter-ideal clauses.
- Route totals for C06: `mathlib` 4, `project-existing` 0, `package-import` 0, `reference-port` 16, `unmatched` 42.

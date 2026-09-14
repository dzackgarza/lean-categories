---
type: reference
title: Provenance contract for FC13 C02
description: '# Provenance contract for FC13 C02'
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
# Provenance contract for FC13 C02

# Provenance contract for FC13 C02

## Provenance contract for FC13 C02

- Canonical source block: FC13 Matsumura Chapter 2, `FC13-C02-U001`–`FC13-C02-U092`, §§4–6 plus the appendix to §6, in canonical source-ID order from [[foundational-corpus-units-fc13-matsumura]]. The generator retrieves the promoted catalogue through `agent-memory`, asserts all 92 IDs occur exactly once and in order, and emits exactly one Sweep-II route per unit.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280` on Lean 4.33.0. Project files are Apache-2.0. `LeanCategories/Algebra/Ideals.lean` already wraps ideal map/comap and localization extension/contraction, and the project has ideal-level primary-decomposition descriptors plus `AffineVarietyDimension`; none owns an entire C02 source row more completely than the pinned interfaces once C02’s extra theorem clauses and module-level generality are enforced. No row is therefore reclassified as `project-existing` merely from a partial wrapper.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, repository `leanprover-community/mathlib4`, Apache-2.0, Lean 4.33.0, and directly project-compatible. The generator asserts the local Mathlib checkout is exactly P and verifies every cited pinned path and declaration token before emitting the chapter record.
- Current Mathlib was independently refreshed on 2026-09-07 to `H=f15b4f161f6ff698ab91b4494faa75925856d0f5`, repository `leanprover-community/mathlib4`, Apache-2.0, Lean 4.34.0-rc2. Current-source and open-PR searches were concentrated on every pinned gap: primary ideals under localization, Theorem 4.3 intermediate-ring recognition, fibre-vanishing and generator loci, catenarity, finite-type dimension=trdeg, Forster–Swan/j-Spec, the Matsumura associated-prime convention, and secondary/attached-prime theory. No exact post-pin declaration closes one of these bundles, so C02 has no `reference-port` route.
- Search channels used project source; pinned P; current H; open Mathlib PRs; Loogle and LeanSearch through the project LeanSearchClient; Mathlib source/docs; Lean Reservoir/indexed web discovery; and discoverable Lean repositories through GitHub code search. No compatible independent package/import owner was found for a C02 gap, so C02 has no `package-import` route.
- Strict bundle semantics were enforced. In particular U008 is not credited without localization preserving primary ideals; U030 is not credited from tensor localization without Tor; U037 is not credited from the free locus alone; U050 is not credited from the algebraically-closed maximal-ideal theorem without the arbitrary-field n-generator clause; and U057 is not promoted from unbundled span-rank ingredients without a source-shaped μ(p,M) interface.
- Associated-prime convention is checked explicitly. Matsumura U066 defines associated primes by exact equality `P=ann(x)` for arbitrary rings. Mathlib’s general predicate uses `P=radical(ann x)` and only proves exact annihilator equivalence under `IsNoetherianRing`. Hence U066, the general clause in U069, and arbitrary-ring U071 remain unmatched, while the Noetherian rows U068/U070/U072–U074 can safely use `isAssociatedPrime_iff` and the associated-prime APIs.
- The secondary-representation appendix U083–U092 was searched independently rather than conflated with associated-prime/primary-decomposition support. No compatible secondary/P-secondary, attached-prime, or secondary-representation API was found; U089 alone maps to the generic lattice predicate `SupIrred ⊤` because that definition is independently exact.
- Route totals for C02 after the 2026-09-14 Mapping repair: `mathlib` 61, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 31. The definitional discovery worklist is now exhausted except U046 catenarity: U033/U044/U057/U059/U061/U063/U066/U077/U083/U085/U086 are direct Mathlib constructions/predicates once theorem clauses are separated from definitions. U046 retains Atlas/AINTLIB catenarity implementations as partial prior art because Matsumura's unrestricted definition also requires existence of finite saturated chains for every comparable prime pair.

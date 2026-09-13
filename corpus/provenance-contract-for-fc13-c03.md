---
type: reference
title: Provenance contract for FC13 C03
description: '# Provenance contract for FC13 C03'
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
# Provenance contract for FC13 C03

# Provenance contract for FC13 C03

## Provenance contract for FC13 C03

- Canonical source block: FC13 Matsumura Chapter 3, `FC13-C03-U001`–`FC13-C03-U073`, §§7–9 including the appendix to §7, in canonical source-ID order from [[foundational-corpus-units-fc13-matsumura]]. The generator retrieves the promoted catalogue through `agent-memory`, asserts all 73 IDs occur exactly once and in order, and emits exactly one Sweep-II route per unit.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280` on Lean 4.33.0, Apache-2.0. Relevant project additions include `LeanCategories/Algebra/ZariskiRing.lean` and ring-level adic-completion topology support. They were treated as owners only when they cover an entire source unit; in particular the project Zariski-ring predicate does not cover all of U053’s terminology/invariance/example bundle, so no row is promoted merely because a partial wrapper exists.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, repository `leanprover-community/mathlib4`, Apache-2.0, Lean 4.33.0, directly project-compatible. The generator asserts the local checkout is exactly P and verifies every cited pinned path/token. Prior FC04 Artin–Rees/completion source-shaped assemblies against this same P were reused only where the FC13 hypotheses and conclusions coincide (notably U043–U048).
- Current Mathlib was refreshed independently on 2026-09-07 to `H=e281a66114fe17935e6ea7917a01b714d0c1e493`, repository `leanprover-community/mathlib4`, Apache-2.0, Lean 4.34.0-rc2. Open-PR searches were concentrated on purity, Hensel factorization, completion Noetherianity/topology, secondary completion packages, Galois conjugacy of primes, and openness of integral extensions. PR #38331 supplies Noetherianity of adic completion but does not close the larger U050/U055 bundles.
- Search channels used project source; pinned P; current H; open Mathlib PRs; Loogle/LeanSearch/Mathlib docs via the repository tooling; Lean Reservoir/indexed discovery; and discoverable external Lean repositories via GitHub code search. No compatible package-import route was found for C03.
- `FC13-C03-U040` has one external `reference-port`: repository `kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509`, path `ClassFieldTheory/Mathlib/RingTheory/HenselPolynomial.lean`, Apache-2.0. Its `MonicCoprimeFactors.liftAdic` construction lifts coprime monic factorizations modulo an ideal in an adically complete ring and records the reductions. That source uses Lean 4.33.0-rc1 and Mathlib `26245e682c354e86f2a4a300812fe4673ae107dc`; because this is close but not the pinned project toolchain/revision, it is a reference to port, not `package-import`.
- Strict bundle semantics were enforced. U004 is not credited from only forward transitivity; U012 is not credited from generic tensor exactness without the intersection+colon theorem; U019 is not credited from the finite local free theorem without the residue-independence/nilpotent clauses; U050/U055 are not credited from only completion Noetherianity; and U069 is not credited from lying-over/incomparability without Galois conjugacy.
- Purity was checked separately. P contains `Ideal.Pure`, but that is the ideal special case defined through a flat quotient; no compatible general pure-submodule API was found. Hence U025–U030 remain unmatched rather than being laundered through ideal purity.
- General linear topology was separated from adic completion. P has filter-basis/submodule-basis linear topologies, supporting U031, but no checked bridge identifies arbitrary presented linear-topology completion with the inverse limit `lim← M/M_λ`; therefore U033–U037 remain unmatched while the I-adic specialization U038 and Noetherian finite-module completion theorems U042–U049 map natively.
- Route totals for C03: `mathlib` 39, `project-existing` 0, `package-import` 0, `reference-port` 1, `unmatched` 33.

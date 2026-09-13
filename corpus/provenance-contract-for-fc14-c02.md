---
type: reference
title: Provenance contract for FC14 C02
description: '# Provenance contract for FC14 C02'
tags:
- project
- reference
timestamp: '2026-09-08T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# Provenance contract for FC14 C02

- Canonical block: FC14 Humphreys Chapter II, `FC14-C02-U001`–`FC14-C02-U064`, exactly 64 unique contiguous rows.
- Search order: project `A=9f23636bbfc1e03147cef3b6ca82cc5701e1f6fb`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current/open Mathlib `H=71a80585ee495fc24472fd0eaffc89d94e4fd8d6`, local packages, broad GitHub Lean search, and `TauCetiProject/TauCeti@74b1b2b2a25467497550234a92ddfc1322a5903f`.
- C02 has 31 pinned `mathlib` rows, 12 `reference-port` rows, and 21 dated `unmatched` rows. Pinned positives: U001, U002, U006, U008, U012, U014, U015, U016, U017, U019, U020, U021, U022, U024, U026, U027, U028, U029, U031, U033, U034, U035, U046, U055, U056, U057, U059, U060, U061, U062, U064. TauCeti reference ports: U030, U032, U038, U041, U044, U045, U047, U048, U049, U050, U051, U063.
- `/tmp/fc14-c02-witness.lean` was compiled against exact P and checked Lie's theorem, Jordan–Chevalley primitives, trace/Killing forms, the semisimple/Killing criteria, derivation/Killing infrastructure, dual/tensor Lie modules, and the pinned Cartan/root-system API. Initial namespace-spelling probes for `killingForm`, `LieDerivation.Killing.exists_eq_ad`, and `TensorProduct.lieModule` were corrected by source inspection; these are naming errors in the scratch witness, not missing declarations.
- `TauCetiProject/TauCeti@74b1b2b2a25467497550234a92ddfc1322a5903f` is Apache-2.0 but pins Lean 4.34.0-rc2 and Mathlib `e21ec05048292b3de86f2a4a300812fe4673ae107dc`; unique hits are therefore `reference-port`, not importable package routes. It supplies Weyl complete reducibility, Schur's lemma, the sl2 highest-weight/classification/Weyl machinery, and positivity of the root-space invariant form.
- TauCeti's universal-enveloping Casimir file explicitly notes that it formalizes the Killing-form Casimir and that Humphreys §6.2 uses the more general trace form of a faithful representation. Accordingly C02 U037 remains unmatched under strict whole-row semantics rather than being over-credited.
- Mathlib's `LieModule.IsTriangularizable` is pointwise triangularizability of each action endomorphism, not Humphreys' simultaneous invariant complete flag. Therefore U003 remains unmatched. Likewise Mathlib's root API is stated for Cartan subalgebras; rows whose source content essentially requires the missing maximal-toral interface (U052–U054, U058) are not promoted merely from adjacent Cartan infrastructure.
- `N=2026-09-08` marks dated unmatched decisions. Strict whole-row semantics apply uniformly.

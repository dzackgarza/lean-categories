---
type: reference
title: Provenance contract for FC14 C05
description: '# Provenance contract for FC14 C05'
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
# Provenance contract for FC14 C05

- Canonical block: FC14 Humphreys Chapter V. Existence Theorem, `FC14-C05-U001`–`FC14-C05-U042`, exactly 42 unique contiguous rows.
- Search order for the active first pass: project HEAD, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current Mathlib `H=e06e14b71d82002ee32ce854c8ec9ebba95f9627`, the live Formalization Corpus under multiple source/type formulations, package/indexed repositories, and current TauCeti `T=4b6fd4b0cef03cc82e7ed38594af21b7bc74c6aa` (Apache-2.0; Lean 4.34.0-rc2; Mathlib `30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe`).
- Route census after first-pass adjudication through U022: 14 `mathlib`, 2 `reference-port`, 26 `unmatched`. Every row has exactly one route.
- Positive rows currently include U001, U002, U003, U004, U005, U006, U008, U019, U020, U021, U022, U023, U030, U031, U032, U035. U004 and U008 are proof-complete current external reference ports; U022 is the direct pinned ambient convention for §18.
- TauCeti is not claimed as directly importable at this project pin: current `T=504ca297404f040f84870b8a624fea1e0ec7e7b8` declares Lean 4.34.0-rc2 and Mathlib `30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe`, so current TauCeti hits remain revision-pinned `reference-port` or partial-reference evidence.
- `N=2026-09-08` marks legacy dated negatives from the initial strict-whole-row pass and is not current first-pass acceptance evidence. On 2026-09-16 U001 was re-read directly in Humphreys §17 and mapped to the pinned arbitrary-field/arbitrary-dimension Lie-algebra interfaces. U004 was re-searched against current TauCeti symmetric-power/invariant/grading files plus Linglib's per-degree map and is now a clause-wise proof-complete reference port; U008 is the current proof-complete TauCeti PBW filtration/associated-graded reference port. U022 was re-read directly in Humphreys §18 and maps to `[Field F] [IsAlgClosed F] [CharZero F] [FiniteDimensional F L] [LieAlgebra.IsSemisimple F L]`, while the free/intermediate Lie algebras intentionally remain unrestricted by `FiniteDimensional`.

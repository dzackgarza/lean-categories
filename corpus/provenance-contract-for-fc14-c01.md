---
type: reference
title: Provenance contract for FC14 C01
description: '# Provenance contract for FC14 C01'
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
# Provenance contract for FC14 C01

# Provenance contract for FC14 C01

- Canonical block: FC14 Humphreys Chapter I, `FC14-C01-U001`–`FC14-C01-U052`, exactly 52 unique contiguous rows.
- Search order: project `A=12618f8abc2b4852b3da9ab65c3bc547ac4c1f19`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current Mathlib `H=71a80585ee495fc24472fd0eaffc89d94e4fd8d6`, current/open/indexed search, Reservoir/packages, broad GitHub Lean repositories, and local reference/mapped corpora.
- C01 has 29 pinned `mathlib` rows, 2 `package-import` rows, and 21 dated `unmatched` rows. Mathlib positives: U001, U002, U003, U004, U005, U006, U012, U013, U015, U016, U018, U021, U022, U023, U024, U025, U027, U028, U030, U032, U033, U035, U039, U043, U045, U046, U047, U048, U049. Package positives: U020, U041.
- `/tmp/fc14-c01-witness.lean` compiles at exact P and checks the central Lie API: Lie algebras/equivalences, ideals/quotients, derivations/adjoint action, derived/lower-central series, radical, nilpotence, Engel, and flags.
- The strongest external hit is `LieLean/LowDimSolvClassification@3c0efe0b3f84f3960c469a84c76fb71162a5d4d5` (Apache-2.0). Its `Classification1.lean` and `Classification2.lean` give Humphreys’ complete dimension-≤2 classification. Its `QuotientSolvable.lean` supplies the extension clause missing from Mathlib’s otherwise complete solvability-closure API. A disposable copy of the full package was rebuilt unchanged against this repository’s Lean 4.33.0 and pinned Mathlib with exit 0, so these are `package-import`, not ports.
- Classical `sl/sp/so` objects exist in Mathlib, but U007–U010 also bundle exact bases/dimension formulas not found as checked declarations; strict semantics keep those rows unmatched. Likewise Mathlib’s generic `Basis.flag` does not by itself supply simultaneous strict triangularization.
- `N=2026-09-07` marks dated unmatched decisions. Strict whole-row semantics apply uniformly.


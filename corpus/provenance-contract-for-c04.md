---
type: reference
title: Provenance contract for C04
description: Extracted from Chapter 2. Modules.
tags:
- project
- reference
timestamp: '2026-09-06T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# Provenance contract for C04

- Project search: `LeanCategories/**` outside `.lake/.agents/.git` was searched first. The project owns source-shaped definitions of primary decompositions, their prime sets, isolated/embedded primes, and ideal extension/contraction.
- Pinned Mathlib: project pin `db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean v4.33.0), denoted `P`, contains the primary-ideal and Lasker APIs cited below; it explicitly documents the first and second uniqueness theorems as Atiyah–Macdonald 4.5 and 4.10.
- Current/open Mathlib: live upstream `29ea5de9cb981cb62dfa7979aaff0851f50c603a` (Apache-2.0), denoted `M`, was refreshed 2026-09-06. Its only change from previously checked `810b3888d0aa94294b18587c453466bc86c1f0fc` is `Mathlib/Combinatorics/SimpleGraph/Maps.lean`, so none of the Chapter-4 algebraic negative judgments changes. Relevant open-PR searches found no owner for the strict gaps.
- External negative search: `rootkiller6788/mini-commutative-homological-algebra@1812d8da6e788d3ee35920a4d23a5d4ede7dfe46` was rechecked; it contains only skeletal/string-level primary-decomposition material for these boundaries, not proofs of the source rows. For localization-preserves-primary, `NeoMathlib@a49fe074238f9c6b38e0c4b25c3fb93c80f605ee` and `duong-ngo/mathlib4@abc669d11b88e163aed1c05b352b5b16889c4ad8` were also checked and have only generic contraction APIs.
- `N` denotes dated 2026-09-06 negative evidence after project-first search, P/M, open/current work, and targeted external Lean search. Concrete examples and strict theorem bundles are not credited from nearby generic infrastructure.

---
type: reference
title: Provenance contract for C07
description: Extracted from Foundational corpus mapping FC04 Atiyah Macdonald.
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
# Provenance contract for C07

- Project search: `LeanCategories/**` outside `.lake/.agents/.git` was searched first. `LeanCategories/Algebra/AtiyahMacdonald/PrimaryDecomposition.lean` supplies project notation for primary decompositions and their prime sets, but the existence and Noetherian theorems in this chapter are owned by pinned Mathlib.
- Pinned Mathlib: project pin `db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean v4.33.0), denoted `P`, contains all 19 routes below. The boundary declarations, number-ring instances, Lasker–Noether interfaces, and associated-prime interfaces were compile-checked in the repository environment.
- Current Mathlib: upstream `5aedf732b6987e8c26ab3c9ebc855314f82b045f` (Apache-2.0), denoted `H`, was rechecked 2026-09-06 and introduces no contrary ownership boundary for these rows. No external route is needed in C07.
- Source normalization: the printed irreducible-ideal definition omits a properness clause, although §7.1 scopes the primary-decomposition discussion to ideals `≠ (1)` and Lemma 7.12 would be false for `(1)` otherwise. U012/U014 therefore use Mathlib `InfIrred`, which makes the source’s necessary implicit properness explicit.

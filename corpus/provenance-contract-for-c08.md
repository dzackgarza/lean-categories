---
type: reference
title: Provenance contract for C08
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
# Provenance contract for C08

- Project search: `LeanCategories/**` outside `.lake/.agents/.git` was searched first. The project reifies Artinian rings as `LeanCategories.Algebra.ArtinianRingCat`, but the theorem-level structure in this chapter is owned by pinned Mathlib.
- Pinned Mathlib: project pin `db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean v4.33.0), denoted `P`, contains the Artinian spectrum, nilpotence, Krull-dimension, localization/product, Nakayama, and cotangent-space interfaces cited below. The assembled U007 and U008 bundles were compile-checked against P; `ZMod (p^n)` synthesizes both Artinian and local structures for prime `p`.
- Current/open Mathlib: upstream `5aedf732b6987e8c26ab3c9ebc855314f82b045f` (Apache-2.0), denoted `H`, was refreshed 2026-09-06 and retains the checked positive interfaces. The strict negative boundaries U010, U012, and U013 were searched in current/open work and broad indexed GitHub Lean code; no complete owner was found.
- `N` denotes dated 2026-09-06 negative evidence after project-first search, P/H, open/current work, installed packages, and targeted external Lean search. Partial positive examples or a two-clause subtheorem do not satisfy a bundled source row.

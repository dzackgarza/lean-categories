---
type: reference
title: Provenance contract for FC12 C03
description: '# Provenance contract for FC12 C03'
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
# Provenance contract for FC12 C03

# Provenance contract for FC12 C03

- Canonical source block: FC12 Beauville, Chapter III, `FC12-C03-U001`–`FC12-C03-U024`, exactly 24 unique contiguous rows.
- Search order: project `A=12618f8abc2b4852b3da9ab65c3bc547ac4c1f19`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d`, current `H=71a80585ee495fc24472fd0eaffc89d94e4fd8d6`, then current/open/indexed Mathlib, packages/Reservoir, broad GitHub Lean search, and local FC06/FC13 mappings/reference corpora.
- C03 has 0 positive routes and 24 dated `unmatched` rows.
- P/H has rational maps, projective schemes/spaces and vector-bundle foundations, but targeted source search found no algebraic `ProjectiveBundle`/projectivization over a scheme, tautological line bundle for it, or geometrically ruled surface API. Therefore `Proj` is not used as a false owner for Beauville’s `P_C(E)` rows.
- No Noether–Enriques theorem, classification of ruled surfaces, rank-two bundle classification on curves, Picard/intersection formulas for ruled surfaces, surface birational invariants, or coherent-sheaf Künneth theorem was found in Mathlib, the project, packages, or broad GitHub Lean search.
- `N=2026-09-07` marks dated unmatched decisions. Strict whole-row semantics apply uniformly.
- **First-pass definitional adjudication (2026-09-15):** U001 and U004 are positive direct-expression routes: Mathlib owns scheme birationality, smooth morphisms and scheme-theoretic fibers, while the project already owns the `Proj`-based projective-space scheme; no extra ruled-surface wrapper is needed. U015/U018/U020 remain `[negative-search-complete]` after current hosted searches for line-bundle extension classes, relative projective bundles/tautological quotients, and the standard surface numerical-invariant package. The old strict-bundle rationale is superseded for these five definition rows only.


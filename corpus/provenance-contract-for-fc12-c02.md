---
type: reference
title: Provenance contract for FC12 C02
description: '# Provenance contract for FC12 C02'
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
# Provenance contract for FC12 C02

# Provenance contract for FC12 C02

- Canonical source block: FC12 Beauville, Chapter II, `FC12-C02-U001`–`FC12-C02-U022`, exactly 22 unique contiguous rows from [[foundational-corpus-units-fc12-beauville|FC12 — Beauville, Complex Algebraic Surfaces, 2nd ed.]].
- Search order: project at `A=12618f8abc2b4852b3da9ab65c3bc547ac4c1f19`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d`, current `H=71a80585ee495fc24472fd0eaffc89d94e4fd8d6`, then current/open Mathlib, indexed services, package/Reservoir discovery, broad GitHub Lean search, and local mapped-source/reference corpora.
- C02 has 0 positive routes and 22 dated `unmatched` rows.
- P and H contain a mature `Scheme.RationalMap`/birational layer, including dense domains and composition. This does not promote U004 because Beauville’s row bundles the rational-map definition with surface-specific finiteness of indeterminacy and divisor/linear-system pullback/image operations that are absent.
- No scheme blow-up exists at P/H. `Mathlib/RingTheory/ReesAlgebra.lean` mentions blow-ups only as future motivation; targeted source search found no geometric blow-up, exceptional divisor, strict transform, Castelnuovo contraction, or factorization of surface birational morphisms. Consequently the blow-up/minimal-model rows are genuine unmatched mappings, not aliases to Rees algebra.
- No divisor linear-system package or Cremona transformation formalization was found in the project, P/H, packages, or broad GitHub search.
- U022 is topology-only but still unmatched: no checked theorem with its compact restriction plus local-homeomorphism hypotheses and uniform neighborhood conclusion was found; the generic local-homeomorphism and compactness ingredients would require a nontrivial finite-subcover argument.
- `N=2026-09-07` marks dated unmatched decisions. Strict whole-row semantics apply uniformly.


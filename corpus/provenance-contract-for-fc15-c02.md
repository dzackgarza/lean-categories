---
type: reference
title: Provenance contract for FC15 C02
description: '# Provenance contract for FC15 C02'
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
# Provenance contract for FC15 C02

- Canonical block: FC15 Humphreys Chapter 2. Classification of finite reflection groups, `FC15-C02-U001`–`FC15-C02-U034`, exactly 34 unique contiguous rows.
- Search order: project `A=9f23636`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current Mathlib `H=71a80585ee495fc24472fd0eaffc89d94e4fd8d6`, current/open/indexed search, packages/GitHub, local corpora, TauCeti `T=74b1b2b2a25467497550234a92ddfc1322a5903f` (Apache-2.0; Lean 4.34.0-rc2; Mathlib `e21ec05048292b3de86d4cf1987e2208171a5642`), plus the externally indexed `coxeter4@881d4302d008284eff8d945990387a3b162cf542` audit.
- Route census: 2 mathlib, 32 unmatched. Every row has exactly one route. Positive rows: U005, U018.
- TauCeti is newer than this project pin, so its matching strong-exchange/Poincaré declarations are `reference-port`, not direct imports. The arithmetic `Mathlib/NumberTheory/HeckeRing` / TauCeti HeckeRing hierarchy is double-coset Hecke theory and is not the Coxeter Hecke algebra of Chapter 7.
- Broad KL/Bruhat search found an external `coxeter4` Bruhat development, but the indexed primary-source audit records active proof placeholders, Lean 4.6.0-rc1 surface mismatch, and no license file; it is not promotable. Separate indexed “Kazhdan–Lusztig” Lean artifacts explicitly identify themselves as statement-shape/model boundaries rather than constructions/proofs.
- `N=2026-09-08` marks scoped negatives for the family `finite/reflection root systems, Coxeter classification and crystallographic types`. Strict whole-row semantics reject adjacent ingredients and executable non-Lean libraries as formalization matches.

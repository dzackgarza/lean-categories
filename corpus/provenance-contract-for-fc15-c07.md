---
type: reference
title: Provenance contract for FC15 C07
description: '# Provenance contract for FC15 C07'
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
# Provenance contract for FC15 C07

- Canonical block: FC15 Humphreys Chapter 7. Hecke algebras and Kazhdan–Lusztig polynomials, `FC15-C07-U001`–`FC15-C07-U044`, exactly 44 unique contiguous rows.
- Search order: project `A=9f23636`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current Mathlib `H=71a80585ee495fc24472fd0eaffc89d94e4fd8d6`, current/open/indexed search, packages/GitHub, local corpora, TauCeti `T=74b1b2b2a25467497550234a92ddfc1322a5903f` (Apache-2.0; Lean 4.34.0-rc2; Mathlib `e21ec05048292b3de86d4cf1987e2208171a5642`), plus the externally indexed `coxeter4@881d4302d008284eff8d945990387a3b162cf542` audit.
- Route census after first-pass definitional adjudication: 9 `mathlib`, 1 `reference-port`, 34 `unmatched`. Every row has exactly one route; no C07 definitional row remains `action=search`/`review` in the canonical index.
- TauCeti is newer than this project pin, so its matching strong-exchange/Poincaré declarations are `reference-port`, not direct imports. The arithmetic `Mathlib/NumberTheory/HeckeRing` / TauCeti HeckeRing hierarchy is double-coset Hecke theory and is not the Coxeter Hecke algebra of Chapter 7.
- Broad KL/Bruhat search found an external `coxeter4` Bruhat development, but the indexed primary-source audit records active proof placeholders, Lean 4.6.0-rc1 surface mismatch, and no license file; it is not promotable. Separate indexed “Kazhdan–Lusztig” Lean artifacts explicitly identify themselves as statement-shape/model boundaries rather than constructions/proofs.
- `N=2026-09-08` marks legacy strict-whole-row negatives and is not current first-pass acceptance evidence. The 2026-09-16 first pass recovered native Coxeter notation/free-module parameters, sign/q notation, distinguished subexpressions, half-power coefficient data, cell relations, and descent sets. `facebookresearch/atlas-lean@e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6` (Apache-2.0) supplies a sorry-free exact reference implementation of the generic left/right multiplication operators (`lambdaOnBasis`, `rhoOnBasis`, `lambdaLift`, `rhoLift`). Its Buildings `GenericAlgebra`/`FreeModuleHeckeData` interfaces take multiplication/laws as fields rather than construct the canonical free-module algebra; the older concrete `HeckeKL.lean` is finite-only (`Fintype W`) and contains admitted later KL identities. Thus U004/U010/U011/U016/U021/U026/U028/U030/U043 remain `[negative-search-complete]` at the exact source-general boundary; fresh cell-module searches returned zero files.

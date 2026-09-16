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
- Route census after first-pass adjudication through U029: 15 `mathlib`, 2 `reference-port`, 25 `unmatched`. Every row has exactly one route.
- Positive rows currently include U001, U002, U003, U004, U005, U006, U008, U019, U020, U021, U022, U023, U024, U030, U031, U032, U035. U025 and U029 now retain clause-specific `[negative-search-complete]` residuals after current ecosystem search.
- TauCeti is not claimed as directly importable at this project pin: current `T=4b6fd4b0cef03cc82e7ed38594af21b7bc74c6aa` declares Lean 4.34.0-rc2 and Mathlib `30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe`, so current TauCeti hits remain revision-pinned `reference-port` or partial-reference evidence.
- `N=2026-09-08` marks legacy dated negatives from the initial strict-whole-row pass and is not current first-pass acceptance evidence. On 2026-09-16 U001/U004/U008/U022 were adjudicated as recorded above. U024 is the pinned free-Lie quotient by the separately named `HH`/`EF`/`HE`/`HF` relator families, `LieSubmodule.lieSpan`, and the canonical Lie quotient. Current TauCeti `T=4b6fd4b0cef03cc82e7ed38594af21b7bc74c6aa` was rechecked for U025/U029: its Serre/minuscule/F4/G2 representations do not implement Humphreys's tensor-algebra model, while `locallyNilpotentSubmodule` supplies the pointwise local-nilpotence predicate but `expAd` still requires uniform `Module.End.IsNilpotent`; hence U025 and U029 retain exactly those two source-specific construction residuals. U024 is then a direct pinned construction from the public `HH`/`EF`/`HE`/`HF` S1–S3 relators, `lieSpan`, and Lie quotient; the later `adE`/`adF` relators are deliberately omitted.

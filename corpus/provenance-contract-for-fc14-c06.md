---
type: reference
title: Provenance contract for FC14 C06
description: '# Provenance contract for FC14 C06'
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
# Provenance contract for FC14 C06

- Canonical block: FC14 Humphreys Chapter VI. Representation Theory, `FC14-C06-U001`–`FC14-C06-U079`, exactly 79 unique contiguous rows.
- Search order: project `A=9f23636` (continuation baseline), pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current Mathlib `H=e06e14b71d82002ee32ce854c8ec9ebba95f9627`, current/open/indexed search, packages, broad GitHub Lean repositories, local corpora, and TauCeti `T=0ce0e8862fb5aeb94a921ab5dc54e2fce17c2d0b` (Apache-2.0; Lean 4.34.0-rc2; Mathlib `30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe`).
- Route census after first-pass adjudication through U022: 11 `mathlib`, 27 `reference-port`, 41 `unmatched`. Every row has exactly one route.
- Positive rows: U001, U002, U003, U004, U005, U006, U007, U008, U009, U010, U011, U012, U014, U015, U016, U017, U018, U020, U022, U025, U026, U028, U030, U032, U033, U035, U036, U037, U038, U041, U043, U044, U052, U053, U061, U063, U072, U077.
- TauCeti is not claimed as directly importable at this project pin: its checked HEAD declares Lean 4.34.0-rc2 and Mathlib `30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe`, so TauCeti hits are conservatively recorded as `reference-port`.
- `N=2026-09-08` marks dated unmatched decisions from the legacy strict-whole-row pass; those are not current first-pass acceptance evidence. On 2026-09-16 U001 was re-read against the Chapter-VI opening and pinned Mathlib: `Field`/`IsAlgClosed`/`CharZero`, `IsSemisimple`, Cartan-subalgebra data, the semisimple→trivial-radical→Killing instance chain, `IsKilling.rootSystem`, `RootPairing.Base`, and `weylGroup` realize the complete standing setting. The generic Lie-module interfaces carry no finite-dimensionality assumption, so only the modules Humphreys declares finite-dimensional receive `FiniteDimensional`. U022 was then rechecked against pinned noncommutative ideal/quotient APIs and current TauCeti: `Ideal U` is already a left ideal, `ker (toSpanSingleton U V v⁺)` is exactly `J(λ)`, and `existsUnique_lieModuleHom_apply_vermaGenerator` proves `vermaIdeal ≤ ker` and constructs the descended map with `Submodule.liftQ`. Atlas's generated primitive-ideal candidate is a different two-sided whole-module annihilator and was rejected. U022 was then re-read against §21.4: pinned `Ideal.torsionOf` is exactly the noncommutative left annihilator `ker (u ↦ u • v⁺)`, and generic `Submodule.factor` supplies the quotient map once the source inclusion `I(λ) ≤ J(λ)` is proved. The inclusion itself is theorem-layer material and is not silently credited to the definition.

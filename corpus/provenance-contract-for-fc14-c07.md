---
type: reference
title: Provenance contract for FC14 C07
description: '# Provenance contract for FC14 C07'
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
# Provenance contract for FC14 C07

- Canonical block: FC14 Humphreys Chapter VII. Chevalley Algebras and Groups, `FC14-C07-U001`–`FC14-C07-U046`, exactly 46 unique contiguous rows.
- Search order: project `A=9f23636` (continuation baseline), pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current Mathlib `H=fcabd43b034f7cc13b777feb1dcc84af140c8ce7`, current/open/indexed search, packages, broad GitHub Lean repositories, local corpora, and TauCeti `T=1bd45176c377ad111517d1e6a51bd9173e8e47e9` (Apache-2.0; Lean 4.34.0-rc2; Mathlib `30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe`).
- Route census after first-pass adjudication through U029: 6 `mathlib`, 17 `reference-port`, 23 `unmatched`. Every row has exactly one route.
- Positive rows: U001, U002, U003, U004, U005, U006, U007, U008, U011, U012, U013, U014, U020, U025, U026, U027, U028, U029, U031, U032, U040, U041, U042.
- TauCeti is not claimed as directly importable at this project pin: its checked HEAD declares Lean 4.34.0-rc2 and Mathlib `30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe`, so TauCeti hits are conservatively recorded as `reference-port`.
- `N=2026-09-08` marks dated unmatched decisions from the legacy strict-whole-row pass and is not first-pass acceptance evidence. On 2026-09-16 U001 was re-read against the Chapter-VII opening and the source-identical FC14-C06-U001 comparison: pinned `Field`/`IsAlgClosed`/`CharZero`, `IsSemisimple`, Cartan-subalgebra data and `IsKilling.rootSystem` realize the complete opening convention. Integral forms and modular reductions are later chapter constructions, not extra fields of U001. U009 was then checked at current TauCeti `1bd45176c377ad111517d1e6a51bd9173e8e47e9`: `IsChevalleySystem.chevalleyLieLattice` is a finite-free full `ℤ`-Lie lattice, while `DynkinType.lieAlgebraBaseChangeEquiv` only identifies `ℚ→K` scalar extension in characteristic zero and its file explicitly leaves positive-characteristic `ℤ→k` base change downstream. No checked indexed source constructs Humphreys's arbitrary-field `L(ℤ)⊗K` as a Lie algebra with the reduced Chevalley table, so U009 is `[negative-search-complete]`. U014 was checked directly at the source's commutative-`F`-algebra generality: pinned `descPochhammer` supplies the falling-factorial numerator and the scalar image of `(k!)⁻¹` supplies the denominator; a local probe over `[Field F] [CharZero F] [CommRing A] [Algebra F A]` elaborated. The recurrence in the same API gives the finite-difference law, so the row is now direct `mathlib` assembly rather than a wrapper gap. U020 is likewise definition-only native assembly: closedness is the first-order `Set` predicate that whenever `root i + root j = root k` with `i,j∈Ψ`, then `k∈Ψ`; current TauCeti's `add_mem_posRoots` and `add_mem_negRoots` are proof-complete examples of exactly this closure condition. U022 was searched against current TauCeti, its roadmap, and the live corpus: the Kostant generators and PBW filtration are formalized, but no proof-complete ordered divided-power/binomial monomial carrier exists, so the height definition remains `[negative-search-complete]`; the roadmap's explicit `pbwMonomial` is admitted. U029 is direct native Mathlib assembly: `Submodule.IsLattice` provides finite generation plus full scalar span, and the source's additional `ℤ`-rank bound is the generic `Module.rank` clause; this is kept explicit because the ambient field is not assumed to be `Frac(ℤ)`.

---
type: reference
title: Provenance contract for FC09 C03
description: '# Provenance contract for FC09 C03'
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
# Provenance contract for FC09 C03

# Provenance contract for FC09 C03

## Provenance contract for FC09 C03

- Canonical source block: FC09 Neukirch Chapter III, `FC09-C03-U001`–`FC09-C03-U129`, in canonical source-ID order from [[foundational-corpus-units-fc09-neukirch]]. The generator retrieves all 129 rows through `agent-memory`, asserts exact order/uniqueness, and assigns exactly one route to every unit.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280` (Lean 4.33.0, Apache-2.0). `LeanCategories/Lattices/Valued/ArithmeticPlace.lean` provides a project sum type of finite and infinite arithmetic places, and `LeanCategories/Lattices/Valued/DeterminantLine.lean` provides generic-rank, determinant-line, intrinsic-discriminant and Steinitz scaffolding. Neither supplies Neukirch's valuation-equivalence-class place object or the replete/Arakelov/metrized structures required by the corresponding C03 bundles, so C03 has no `project-existing` route.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0. Native source-complete coverage in C03 is concentrated in the global product formula/class group, trace-dual/different theory, Kähler differentials, Hermite–Minkowski discriminant theorems, the no-unramified-extension theorem for ℚ, and the abstract projective-module lifting criterion.
- Current Mathlib was checked at `H=71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. Targeted current-tree searches found no `Arakelov`, `replete ideal`, `Euler-Minkowski`, or `Grothendieck-Riemann-Roch` layer. The current different file still has no Kähler-differential bridge identifying the different with the annihilator of Ω, and no first-class relative `discriminantIdeal` was found. Targeted open-PR title searches on 2026-09-07 likewise found no relevant arithmetic-metric or different/Kähler owner; the returned Kähler and Hermite hits concern refactors or Hermite polynomials, not these source units.
- Strict bundle semantics was enforced. In particular, ordinary finite/infinite place representations do not earn U001–U005 where Neukirch packages valuation classes and a nonstandard convention declaring C/R unramified; generic divisor/Picard infrastructure does not earn replete/Arakelov ideals; transitivity of the different alone does not earn U028's localization-and-completion bundle; derivative membership does not earn U032's generation theorem; the prime-divides-different criterion does not earn U033's tame/wild exponent formulas; Kähler infrastructure does not earn U036 without the annihilator equality; and absolute discriminant identities do not earn U038–U043's relative discriminant-ideal package.
- The arithmetic-metric half of the chapter is treated just as strictly. The project determinant-line API does not earn metrized determinant sequences; generic tensor/Hermitian/projective/Picard APIs do not earn the metrized-module category; and ordinary Grothendieck/homological APIs do not earn arithmetic K₀, arithmetic Chern character, Grothendieck–Riemann–Roch, or Euler–Minkowski statements.
- Short derivations are credited only from exact pinned ingredients: U031 collapses the conductor in `conductor_mul_differentIdeal` under the monogenic hypothesis; U045 derives Neukirch's weaker uniform discriminant bound from Mathlib's sharper signature-dependent bound using `r+2s=n`; U047 specializes Hermite finiteness to a fixed algebraic closure; and U083 uses the standard equivalence between Hom-exactness and lifting against surjections.
- All `mathlib` targets were path/token validated against P; current-head negative checks were validated against H.
- Route totals for C03: `mathlib` 11, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 118.


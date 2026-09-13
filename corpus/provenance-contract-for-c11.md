---
type: reference
title: Provenance contract for C11
description: '# Provenance contract for C11'
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
# Provenance contract for C11

# Provenance contract for C11

- Project search was performed first at repo HEAD `351cba0287077eadfcd7c71a78ec4a509ce8c966`. `LeanCategories/Algebra/DimensionTheory.lean` is the project owner for exactly three source-facing definitions used here: `LeanCategories.Algebra.PoincareSeries` (U002), `LeanCategories.Algebra.IsSystemOfParameters` (U034), and `LeanCategories.Algebra.AffineVarietyDimension` (U047). The file's current content was read from HEAD rather than inferred from earlier vault snapshots, and it compiled successfully in the project environment. Its `HilbertFunction` is the raw coefficient function and therefore is not the source's eventual Hilbert polynomial in U007.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean v4.33.0). P contains the exact length/additivity, regular-element, ideal-height/Krull-height, regular-local, polynomial-regularity, affine function-field, Nullstellensatz, and scheme-stalk dimension APIs cited in the chapter. The U026 source-shaped system-of-parameters existence assembly was compiled against P. A declaration probe covering U029/U032/regular-local/polynomial-dimension interfaces also compiled against P.
- Current Mathlib is `H=5aedf732b6987e8c26ab3c9ebc855314f82b045f` (Apache-2.0), rechecked on 2026-09-06. H still has no graded-module Hilbert–Serre theorem, no Hilbert–Samuel eventual-polynomial construction, no theorem that regular local rings are preserved/reflected by adic completion, and no theorem equating local Krull dimension of finite-type integral affine algebras with transcendence degree. Direct `git grep` at H found only the generic `Polynomial.hilbertPoly` backend for the first family of gaps and no owners for the latter two families.
- `Mathlib/RingTheory/Polynomial/HilbertPoly.lean` is deliberately only a backend: it proves eventual coefficient identities for a rational function already presented as `p/(1-X)^d`, e.g. `Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval`. It does not derive such a rational form from a finite graded module. Therefore it does not satisfy U003, U005, or the Hilbert–Samuel rows U012–U021/U027.
- Current external Hilbert–Samuel search rechecked `ImperialCollegeLondon/FLT@8ec873aab84b21c4faaef849d5afd56ef79f684d` (Apache-2.0; Lean `v4.34.0-rc2`; Mathlib `c4a007f4389f67c1f224c4b87984a3470754b53f`). `FLT/Slop/DimensionTheorem/Defs.lean`, `DimEqDelta.lean`, `GrowthLeDelta.lean`, and `Main.lean` define the exact least-generator invariant `minGenPrimary` and prove its equality with Krull dimension and with a growth-order invariant. The development explicitly states that it does **not** construct the Hilbert–Samuel polynomial or formalize Hilbert–Serre; `growthDeg` is intentionally a replacement. Hence these files are useful negative evidence, not exact reference ports for the source polynomial-degree rows.
- GitHub indexed Lean search for `HilbertSerre`, graded Hilbert series, Hilbert–Samuel polynomiality, and characteristic-polynomial length growth found no exact owner beyond Mathlib's rational-function backend and FLT's explicit growth-order substitute. The external FLT head was checked immediately before assembly.
- Current regular-completion search checked P/H and indexed external Lean. No exact theorem `IsRegularLocalRing A ↔ IsRegularLocalRing Â` or equivalent was found. `Mathlib/RingTheory/Regular/RegularSequence.lean` still contains a TODO to apply the relevant regular-sequence theory to localization and completion. `DE0CH/flt-lean@a5ec7082457bab42553702cdb183b3e034021ab3` was rechecked; its `Fermat/FLT/GaloisRepresentation/HardlyRamified/CompleteLocalNoetherian.lean` proves complete-local Noetherianity from finite generation of the maximal ideal, not preservation of regularity or the coefficient-field power-series theorem required by U042/U044.
- Current affine-dimension search at P/H and indexed external Lean found no theorem containing a Krull-dimension/transcendence-degree bridge for the source finite-type integral affine setting. The project therefore owns only the trdeg definition U047; pinned Mathlib separately owns function fields, Nullstellensatz point/maximal-ideal correspondence, and local/stalk Krull dimension. Their absence of a connecting theorem is the reason U050/U051/U053 remain unmatched.
- For U052, P supplies `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`, going down for integral extensions over integrally closed domains, prime-chain lifting via `Ideal.exists_ltSeries_of_hasGoingDown`, and `IsLocalization.AtPrime.ringKrullDim_eq_height`. No checked theorem or compiled source-shaped assembly gave equality of the two localized dimensions under exactly the source hypotheses without adding Noetherian assumptions, so the whole row remains unmatched.
- `N` denotes dated 2026-09-06 negative evidence after project-first inspection, P, H/current Mathlib, relevant open/current work, and targeted external Lean search. A theorem phrased in a substitute invariant (`growthDeg` instead of Hilbert–Samuel polynomial degree), one direction of a biconditional, or a collection of adjacent ingredients without a checked whole-row assembly is not credited under strict bundle semantics.

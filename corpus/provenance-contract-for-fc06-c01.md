---
type: reference
title: Provenance contract for FC06 C01
description: '# Provenance contract for FC06 C01'
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
# Provenance contract for FC06 C01

# Provenance contract for FC06 C01

## Provenance contract for FC06 C01

- Canonical source block: FC06 Hartshorne, Chapter I, `FC06-C01-U001`–`FC06-C01-U147`, in canonical source-ID order. The source catalogue was not altered by this remap.
- This contract was re-audited clause by clause on 2026-09-13 after the 2026-09-06 whole-row matching rule was found invalid. A row is now direct when the conjunction of checked declarations realizes its clauses; a row is `partial` when reusable owners exist but a material comparison/bridge remains; `unmatched` is reserved for rows whose substantive clauses remain absent after the full search surface is exhausted.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Lean 4.33.0, Apache-2.0). Current upstream was refreshed by `git ls-remote`/fetch on 2026-09-13 at `H=87befc843c2b3a1be12f7fe9ba274d212b544348`. Project source, the prior source atlas/Reservoir discoveries, current/open Mathlib, GitHub Lean code search, and targeted open-PR search were all used in the remap; dated negative rows state this refreshed search rather than relying on the old packaging rule.
- The central correction is the classical Nullstellensatz block. `FC06-C01-U013` is assembled from `MvPolynomial.zeroLocus_anti_mono`, `vanishingIdeal_anti_mono`, `zeroLocus_vanishingIdeal_galoisConnection`, `vanishingIdeal_zeroLocus_eq_radical`, `vanishingIdeal_pointToPoint`, `PrimeSpectrum.vanishingIdeal_union`, and `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`. `FC06-C01-U015` uses the same Galois connection and radical equality together with `PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical` / `isIrreducible_iff_vanishingIdeal_isPrime`. Both are direct Mathlib routes in Hartshorne’s classical point-set setting.
- Other early classical rows also changed materially: `U001` is the existing point type `Fin n → k`; `U011` is the conjunction of `IsClosed`, `IsIrreducible`, and relative `IsOpen`; `U019` combines `isMaximal_iff_eq_vanishingIdeal_singleton` with coordinate-polynomial uniqueness; `U021` is `MvPolynomial.vanishingIdeal` followed by `Ideal.Quotient`; and `U038` is exactly Mathlib `Projectivization`. These rows do not justify project-local wrapper definitions merely because the textbook gives them names.
- Projective algebraic geometry is mapped through bundled homogeneous owners wherever possible. `ProjectiveSpectrum.vanishingIdeal` returns `HomogeneousIdeal` directly; `ProjectiveSpectrum.zeroLocus_iSup_homogeneousIdeal`, `zeroLocus_mul_homogeneousIdeal`, and the Zariski topology supply the projective closed-set calculus. Consequently `U045` maps to `HomogeneousIdeal` plus `Ideal.Quotient`; the existing repo-local pattern “plain `Ideal` + separate homogeneity proof” is specifically not the canonical route.
- The scheme interfaces are accepted when they genuinely generalize the source and the comparison is explicit. Affine `Spec.homEquiv` / `AffineScheme.equivCommRingCat`, `AffineSpace.homOverEquiv`, standard affine/projective basic-open localization isomorphisms, structure-sheaf sections/stalks, residue fields, and `Scheme.functionField` now appear directly or as partial routes in `U046`–`U077`. A missing classical closed-point bridge is recorded as the remaining comparison; it no longer erases the reusable general theorem.
- Function-field rows reuse `Scheme.germToFunctionField_injective`, stalk `IsFractionRing` instances, `RationalMap.equivFunctionField`, `Scheme.Birational`, and the separated-target equalizer machinery. Rows stay partial only when the source additionally asks for a classical curve-model or explicit field-homomorphism comparison not exported by those declarations.
- The valuation/DVR/Dedekind block `U109`–`U116` remains direct pinned Mathlib. `U117` is now partial rather than unmatched: `IsIntegralClosure.finite` / `isDedekindDomain` supply the separable case, while Hartshorne’s arbitrary finite-extension hypothesis is still broader.
- Current open Mathlib work invalidates two former negative conclusions. PR #39289 at `7c2cce3eff4d42f292ba86215e7e3fa10735e925` contains `Mathlib/RingTheory/CohenStructureTheorem.lean`, including `exists_isCohenRing_residueField_map_bijective` and `exists_mvPowerSeries_surjective_of_residueField_map_bijective`; PR #35560 at `1e4c8c2848f36bd73aea213044612c247b1ea91f` adds regular-local/power-series and `AdicCompletion.ringKrullDim_eq` corollaries. `U101` is therefore a `reference-port`, `U103` is a completion-dimension `reference-port`, and `U104` is partial on that PR stack.
- Likewise the graded Hilbert-polynomial theorem is not absent: open PR #9819 at `413e5b872a7c758e0eb91f99cb96d6a61c81f0a2` supplies `hilbertPolynomial`, `AdditiveFunction_eq_hilbertPolynomial_eval`, `exists_unique_hilbertPolynomial`, and `natDegree_hilbertPolynomial`. `U139`–`U140` are reference-port routes and `U141`/`U142` reuse that owner clause by clause.
- The refreshed negative searches remain substantive rather than packaging-based. No compatible algebraic-geometric blowup/strict-transform implementation was found for `U083`–`U091`; GitHub code search still returns only Rees-algebra comments or unrelated uses of “blowup”. No compatible Hartshorne numerical-polynomial definition/basis theorem was found for `U133`–`U134`. No checked source supplies the specific projective-model/desingularization/valuation-curve existence theorems retained as unmatched in `U125`, `U127`–`U129`, nor the Bézout equalities `U144`–`U145`.
- `U135` is now partial: Mathlib already owns `GradedModule`, graded-object shifts, and `Module.annihilator`; only the homogeneity theorem for the annihilator was not found. `U137` is direct because its multiplicity is simply `Module.length` after localization. `U143` is direct as a definition assembled from ideal quotient/sum, localization, and module length.
- All remaining `unmatched` rows in this chapter were rechecked against project source, pinned Mathlib, current upstream `H`, open PRs, GitHub Lean code search, the existing Reservoir/package discoveries, and the formalization atlas. Their mapping rows now state the missing substantive theorem/construction rather than requiring a single packaged declaration.

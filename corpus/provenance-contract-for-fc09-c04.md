---
type: reference
title: Provenance contract for FC09 C04
description: '# Provenance contract for FC09 C04'
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
# Provenance contract for FC09 C04

# Provenance contract for FC09 C04

## Provenance contract for FC09 C04

- Canonical source block: FC09 Neukirch Chapter IV, `FC09-C04-U001`–`FC09-C04-U083`, in canonical source-ID order from [[foundational-corpus-units-fc09-neukirch]]. The generator retrieves all 83 rows through `agent-memory`, asserts exact order/uniqueness, and assigns exactly one route to every unit.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280` (Lean 4.33.0, Apache-2.0). `LeanCategories/Algebra/IdealProfiniteCompletion.lean`, `LeanCategories/ForMathlib/AdicCompletionTopology.lean`, and `LeanCategories/ForMathlib/DenseIntegralCompletion.lean` provide explicit ideal-adic inverse-limit infrastructure. Only U019 closes as `project-existing`: it reuses the already validated FC09-C02 `ℤ_p` inverse-limit equivalence. The project has no class-formation/reciprocity or Herbrand layer.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0. Native C04 coverage includes absolute/infinite Galois groups, Krull topology and infinite Galois correspondence, categorical TopCat limits/colimits, profinite groups and profinite completion, multiplicative/Noether Hilbert 90, low-degree group cohomology, the Tate long exact sequence, and coinduced representations/Shapiro.
- Current Mathlib was checked at `H=71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. It still has no `periodicTateCohomology`, `herbrandQuotient`, or merged `Mathlib/NumberTheory/CFT/ClassFormation/Basic.lean`. Open Mathlib PR #42687 was inspected at `O=a40561e249ebf45d2870f5d9d45bc2eb4d80b242`: it defines modern `Formation`, `FieldFormation`, and `ClassFormation` structures, but contains no reciprocity theorem/norm-residue isomorphism, and its proposed local class-formation instance in `Local.lean` remains sorried. Consequently it does not close Neukirch U043–U078.
- External Lean discovery found `kbuzzard/ClassFieldTheory` at `R=ccc3323c6750abca25b49b35106f54eb3a398509` (Apache-2.0), whose root package pins Mathlib `26245e682c354e86f2a4a300812fe4673ae107dc`. The exact no-`sorry` files used here prove cyclic Tate periodicity, the explicit `H^-1 ≃ H^1` comparison, Tate-acyclicity of induced representations plus the normal-basis identification, and the Herbrand quotient theorems. Because that package is pinned to a distinct Mathlib revision and was not validated as a drop-in dependency at P, these are conservatively recorded as `reference-port`, not `package-import`.
- Strict bundle semantics was enforced. Finite-field Frobenius APIs do not earn U002 or U022 without the absolute-Galois/profinite-integer identification; generic TopCat limits do not earn U012–U016, which require compatible topological-group structures or exactness; the adic valuation-ring inverse limit does not earn U020 because that row also asserts the full unit-group inverse limit; profinite completion does not by itself earn the explicit `\widehat{ℤ}=lim ℤ/nℤ` and procyclic classifications U021–U024; cyclic Kummer APIs do not earn the abstract/general-abelian Kummer bundles U035–U039; and local ramification/valuation APIs do not earn Neukirch’s abstract class-field axioms or reciprocity/existence theorems.
- Short derivations are credited only where the checked interfaces close the full row. U006 translates between Mathlib’s compact-totally-disconnected model and Neukirch’s open-normal-neighborhood model; U008–U011 use the categorical encoding of directed systems and TopCat’s explicit limit/colimit constructions; U037 transports Tate-acyclicity across the external normal-basis induced-representation isomorphism; U079 takes the six relevant consecutive terms of Mathlib’s Tate long exact sequence; U082 translates left/right covariance by inversion; and U083 combines external 2-periodicity with pinned Shapiro in ordinary degrees 2 and 1.
- All `mathlib` targets were path/token validated against P, the U019 project targets against A, every `reference-port` target against R with `sorry` excluded in the cited files, and current/open negative checks against H/O.
- Route totals for C04: `mathlib` 17, `project-existing` 1, `package-import` 0, `reference-port` 5, `unmatched` 60.


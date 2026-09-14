---
type: reference
title: Provenance contract for FC08 CD
description: '# Provenance contract for FC08 Appendix D'
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
# Provenance contract for FC08 Appendix D

- Canonical source block: FC08 Lee, Appendix D, `FC08-CD-U001`–`FC08-CD-U011`, exactly 11 unique catalogue rows.
- The 2026-09-14 exact-route remap replaces the obsolete strict-whole-row audit. Current totals are `mathlib` 5, `project-existing` 0, `package-import` 0, `reference-port` 2, `unmatched` 4.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`; current Mathlib was inspected at `H=2ff8073df352b7cb74638403c464ed5cd3f97ce2`. Current TauCeti was inspected at `T=39d3c8522a6685aa5ffe7cdb74b2465530e990a0` (Apache-2.0, Lean 4.34.0-rc2, Mathlib `30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe`). The relevant TauCeti ODE files are unchanged between the cached proof-complete revision and `T`; source checks found no `sorry`, `admit`, or custom `axiom`.
- U003 is now a reference port rather than a gap. TauCeti's `ODE.exists_contDiffAt_localFlow` supplies a jointly smooth local autonomous flow with the ODE and flow law in finite dimension; pinned Mathlib's `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless` supplies common-interval uniqueness for the smooth field. Product-neighborhood shrinking and time translation match Lee D.1.
- U009 is likewise a reference port. Apply the same smooth local-flow theorem to the standard autonomous extension `W(s,x)=(1,V(s,x))`; the first coordinate is translation in time and the second coordinate gives Lee's nonautonomous solution. This converts smooth dependence on extended initial state and elapsed time into smooth dependence on `(t,t₀,c)`. TauCeti is not marked `package-import` because its Lean/Mathlib pins differ from this repository's pinned environment.
- U005 is positive without TauCeti: local Lipschitz data shrink to a ball with one Lipschitz constant and a norm bound, `IsPicardLindelof.of_time_independent` packages those hypotheses, and `exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt` gives a common local family. U010 is also a native assembly from the chain rule, interval substitution, and the fundamental theorem of calculus.
- Four residuals remain. U004 needs Lee's nonlinear scalar comparison theorem rather than Mathlib's linear Gronwall bound. U007 needs propagation of local uniqueness over an arbitrary common domain under merely local-Lipschitz hypotheses. U008 now has TauCeti's local smooth-flow germ as a supplied ingredient, but no theorem identifies an arbitrary supplied solution family with such germs across all of `J₀ x U₀`. U011 has native generalized-eigenvector infrastructure but no checked full `2 x 2` constant-coefficient ODE/Jordan-case classification.
- Negative findings are scoped to the inspected pinned/current Mathlib and current TauCeti sources; no failed search endpoint is used as evidence of absence. Definitions remain blocked by `remap-strict-bundle`.

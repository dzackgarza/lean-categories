---
type: reference
title: Provenance contract for FC07 C01
description: '# Provenance contract for FC07 C01'
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
# Provenance contract for FC07 C01

# Provenance contract for FC07 C01

- Canonical source block: FC07 Hatcher, Chapter 1, `FC07-C01-U001`–`FC07-C01-U094`, exactly 94 contiguous rows extracted from [[foundational-corpus-units-fc07-hatcher|FC07 — Hatcher, Algebraic Topology]] through `agent-memory`.
- Search order followed the corpus plan: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, then pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=633b366493a76df88a2bff099ed0cbf711a59ec9` (Apache-2.0, Lean 4.34.0-rc2), current/open work and indexed searches, Reservoir/packages, broad GitHub/discoverable Lean, and local reference mirrors. No `project-existing` C01 owner was found.
- Every explicit Mathlib path/declaration cited by the C01 table was rechecked in the project checkout at exact pin `P`; all 39 distinct `Mathlib/...lean::declaration` references resolve there, and a batch Lean `#check` of the credited pinned declarations succeeds under that checkout. The TauCeti and sphere-six target paths were likewise rechecked at `T=2db3a983be93975cbf1d54bcc7d6ae1b97830856` and `R=895c0a0661501581c34d42fea3c553d4f0ee43b1`.
- The previously promoted FC02 Munkres fundamental-group, covering-classification, and graph audits were retrieved through `agent-memory` and reused where their source statements coincide. Their declaration/path checks were refreshed only where FC07’s unit is stricter or TauCeti has since acquired a sharper owner.
- TauCeti was refreshed to upstream `T=2db3a983be93975cbf1d54bcc7d6ae1b97830856` (Apache-2.0, Lean 4.34.0-rc2, Mathlib `5fcc6656691ed31965746c369f41fa75e567ac9d`). It supplies source-shaped product/sphere π₁, universal-cover classification, subgroup realization, monodromy/index, deck/regular-cover, and quotient-action results. Because its Mathlib/toolchain are post-pin, every credited TauCeti route is `reference-port`.
- `deancureton/sphere-six-complex@895c0a0661501581c34d42fea3c553d4f0ee43b1` (Apache-2.0, Lean 4.34.0-rc1) is reused for deformation-retract/homotopy-equivalence data in U026 and remains `reference-port`.
- `harfe/fixed-point-theorems-lean4@770940ddf9878cf61952ed53d910b92bca841838` (MIT, Lean/Mathlib 4.32.0, Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`) supplies Brouwer fixed point for U017 as a stronger theorem, hence `reference-port`. Broad searches still found no completed Borsuk–Ulam owner for U018/U019.
- `Arthur742Ramos/ComputationalPathsLean@f90943eecdde516817fbc33863486b681a0a9645` is MIT, Lean 4.33.0, and pins exactly `P`; its targeted circle module builds at that revision. It proves an `AddCircle` winding classification, but U013 names Hatcher’s literal Euclidean cos/sin loop and no checked bridge to that exact generator was found, so U013 remains unmatched despite package compatibility. Its computational-path Bass–Serre API is also not conflated with Hatcher’s topological KΓ construction.
- `finite-graph-fundamental-group@dd57e3ab8bc5a7042fcc5498e778b008d87ac032` and `GraphCoveringTheory@c918a72c5170503c98fd66a0f3116b7bfcd1250c` are Apache-2.0, Lean/Mathlib 4.32.0 reference ports whose targeted builds were already verified in FC02. They give finite graph realization/tree contraction/free-basis/Schreier results. Hatcher’s graph rows are stated for arbitrary 1-dimensional CW graphs; finite specializations are therefore retained as adjacent evidence rather than promoted unless the whole source row is owned.
- Pinned Mathlib’s `FreeGroupBasis` plus `Equiv.ofFreeGroupEquiv` is sufficient for U031: any two basis index types of the same free group are equivalent, so rank is well-defined. Pinned `subgroupIsFreeOfIsFree` owns Nielsen–Schreier U077 directly.
- U032 is not promoted from the open van-Kampen work or ComputationalPaths pushout SVK: Hatcher’s row is the full arbitrary-cover/triple-intersection theorem and must be owned as a bundle. The same rule blocks U033/U038 and the KΓ rows when only their algebraic pushout/HNN ingredients are formalized.
- U043–U061 are checked against the current TauCeti connected-cover stack. In particular, U046 combines pinned covering-map injectivity with TauCeti’s monodromy stabilizer/range theorem; U047 is `card_fiber_eq_index`; U052–U054 are the subgroup-cover and pointed/unpointed classification equivalences; U058 is normality plus the normalizer/deck quotient; U061 combines Mathlib’s quotient-covering fundamental-group equivalence with TauCeti regularity and full-deck-group identification.
- U062 remains unmatched deliberately: Mathlib’s standalone `ProperlyDiscontinuousSMul` is a stronger compact-set notion under local compactness/T2 assumptions, while `IsQuotientCoveringMap.disjoint` bakes in quotient-map/orbit data. Neither declaration is exactly Hatcher’s bare local pairwise-disjoint-translate definition together with the free-action definition.
- U078–U087 remain unmatched under source semantics. TauCeti defines K(G,1) through asphericity/higher homotopy and proves universal covers weakly contractible; Hatcher’s catalogue row explicitly requires a contractible universal cover. No checked Whitehead/CW bridge was found that turns those APIs into the complete source bundle, and concrete RP∞/lens/surface/knot/EG examples are not credited from generic ingredients.
- U092/U093 record Mathlib’s exact algebraic amalgamated-product/HNN constructions only as adjacent evidence: the units assert topological π₁(KΓ) computations, and no checked KΓ bridge was found.
- `N=2026-09-06` denotes a dated unmatched result after the prescribed search layers. Strict whole-row semantics are applied uniformly.


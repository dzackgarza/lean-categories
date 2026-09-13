---
type: reference
title: Provenance contract for FC07 C04
description: '# Provenance contract for FC07 C04'
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
# Provenance contract for FC07 C04

# Provenance contract for FC07 C04

- Canonical source block: FC07 Hatcher, Chapter 4, `FC07-C04-U001`–`FC07-C04-U188`, exactly 188 unique contiguous rows retrieved from [[foundational-corpus-units-fc07-hatcher|FC07 — Hatcher, Algebraic Topology]] through `agent-memory`.
- Search order followed the mapping plan: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, then pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=80cbd0498ab39e21d24d6730b3f932cec672a702` (Apache-2.0, Lean 4.34.0-rc2), current/open work and indexed searches, Reservoir/package discovery, broad discoverable Lean repositories, and local mirrors. No `project-existing` C04 owner was found.
- Every promoted Mathlib declaration/path was compiled through the project toolchain at the exact pin `P`; every cited source path was also verified with `git cat-file` at the pinned git object. C04 therefore uses only `mathlib` and `unmatched` routes: 5 pinned positive rows and 183 dated unmatched rows.
- The exact pinned positives are U001 (homotopy groups as boundary-relative cube loops with concatenation group law), U055 (fiber bundles and local trivializations), U069 (complex unitary and quaternionic unitary/symplectic groups), U141 (oriented-graph diagrams of spaces and their amalgamation as a topological colimit), and U150 (pushout as the quotient of a disjoint sum with the final topology).
- U056 is deliberately not promoted: `IsFiberBundle.isCoveringMap`/`FiberBundle.isCoveringMap` establish only discrete-fiber bundle ⇒ covering map, while the source row states the two-way characterization. U083 is likewise not promoted: covering maps have a checked homotopy-lifting theorem, but no general topological Hurewicz-fibration predicate with HLP for every space was found.
- U069 is routed through the actual star-unitary interface, not `Matrix.symplecticGroup`. `Matrix.unitaryGroup` and `mem_unitaryGroup_iff'` own U(n), while generic `unitary` specializes to quaternionic matrices because `Quaternion` carries the standard ring and star structures; this is the compact quaternionic unitary group convention denoted Sp(n) by Hatcher. The algebraic standard-alternating-form `Matrix.symplecticGroup` is a name-adjacent but different object and is not cited.
- U141 is an equivalent categorical formalization of Hatcher’s quotient construction, not an abstract-name match: `Prefunctor` records vertex objects and edge maps, `Paths.lift` freely extends an oriented-graph diagram, `ColimitType` is the quotient of the sigma/coproduct of object elements by generated diagram-map identifications, and TopCat supplies the final topology. U147 remains unmatched because its second clause requires a homotopy-colimit/realization interface, which was not found.
- U150 is literal at the underlying-set level: `Types.Pushout.Rel` identifies `inl (f z)` with `inr (g z)` and `Types.Pushout` is `Quot` by that relation; the TopCat colimit construction supplies the quotient/final topology.
- Model-category `Fibration`/`Cofibration` declarations are not credited for Hatcher’s topological HLP/HEP notions (U083, U148–U149). Likewise analytic/ring spectra, spectral sequences, Dold–Kan, and Eilenberg–Steenrod axioms are not algebraic-topological spectra, Dold–Thom, or Steenrod operations.
- Current upstream was refreshed on 2026-09-07: `H=80cbd0498ab39e21d24d6730b3f932cec672a702` is the newest Mathlib commit returned by the repository commit feed at audit time, and its `lean-toolchain` is Lean 4.34.0-rc2. Current code search still finds no Steenrod-operation implementation; “Steenrod” reaches only `Mathlib/AlgebraicTopology/EilenbergSteenrod.lean`, while “Hurewicz” reaches the covering-space lifting API rather than the Hurewicz theorem.
- Broad external Lean-4 discovery did not identify a complete owner for the missing Whitehead/Hurewicz/Blakers–Massey/Postnikov/K(G,n)/Brown-representability/stable-homotopy/Dold–Thom/Steenrod rows. Search results with theorem names in plans, future-work notes, other proof assistants, or semantically unrelated uses were not credited.
- The canonical catalogue has exactly one FC07 block after C04: Appendix `CA`, `FC07-CA-U001`–`FC07-CA-U032`, 32 unique contiguous rows. No additional numbered Hatcher chapter is present in the catalogue.
- `N=2026-09-07` denotes a dated unmatched result after the prescribed search layers. Strict whole-row semantics are applied uniformly: specializations, adjacent algebra, isolated clauses/examples, and unbridged alternative representations do not count.


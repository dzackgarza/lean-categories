---
type: reference
title: Provenance contract for FC07 C02
description: '# Provenance contract for FC07 C02'
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
# Provenance contract for FC07 C02

# Provenance contract for FC07 C02

- Canonical source block: FC07 Hatcher, Chapter 2, `FC07-C02-U001`–`FC07-C02-U098`, exactly 98 contiguous rows retrieved from [[foundational-corpus-units-fc07-hatcher|FC07 — Hatcher, Algebraic Topology]] through `agent-memory`.
- Search order followed the mapping plan: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, then pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=633b366493a76df88a2bff099ed0cbf711a59ec9` (Apache-2.0, Lean 4.34.0-rc2), current/open work and indexed searches, Reservoir/package discovery, broad GitHub/discoverable Lean, and local mirrors. No `project-existing` C02 owner was found.
- Every promoted Mathlib declaration/path was compiled through the project toolchain at the exact pin `P`; exact source files were also checked in the pinned git object. C02 therefore uses only `mathlib` and `unmatched` routes: 20 pinned positive rows and 78 dated unmatched rows.
- The pinned singular-homology stack supplies `TopCat.toSSetObjEquiv`, `singularChainComplexFunctor`, `singularHomologyFunctor`, the H₀/path-component theorem, and topological homotopy invariance. Generic homological algebra supplies chain complexes/homology maps, chain-homotopy invariance, exact/short-exact complexes, connecting morphisms, and the three exactness pieces of the long exact homology sequence. These are credited only where they own the entire Hatcher unit.
- Current Mathlib `H` adds `Mathlib/AlgebraicTopology/SimplicialSet/Homology/Relative.lean`: `SSetPair.chainComplex`, `SSetPair.homology`, `SSetPair.homologyFunctor`, `SSetPair.homologyδ`, and `homology_exact₁/₂/₃`. This is relative homology of simplicial-set monomorphisms. No checked functor/bridge from `TopPair` or singular topological pairs to `SSetPair` was found, so it is adjacent post-pin evidence rather than a `reference-port` owner for U026/U031–U033/U037/U039/U042/U071.
- `Mathlib/AlgebraicTopology/EilenbergSteenrod.lean` at P/H defines `TopPair.HomologyPretheory` (absolute/relative functors plus boundary transformations) and separately `IsHomotopyInvariant`; it does not package the exactness, suspension, wedge/additivity, and dimension axioms required by Hatcher U075, hence U075–U077 remain unmatched.
- `Mathlib/Algebra/Homology/EulerCharacteristic.lean` at P/H defines algebraic `HomologicalComplex.eulerChar` and `homologyEulerChar`, but contains no theorem identifying them and no CW-cell-count/singular-homology bridge. It therefore does not own U064/U065. Sheaf-cohomology Mayer–Vietoris files likewise are not singular-homology routes for U067–U070.
- `harfe/fixed-point-theorems-lean4@770940ddf9878cf61952ed53d910b92bca841838` (MIT; Lean 4.32.0; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`) proves Brouwer fixed point on every nonempty compact convex subset of a finite-dimensional real normed space. It covers the fixed-point clause of U025, but the row also asserts arbitrary-dimensional disk no-retraction, and no checked declaration in that package supplies it; strict bundle semantics therefore leave U025 unmatched.
- `mccorvie/classification-of-surfaces@e3c7230fe78d7b056a415d9ecae6f77887046b32` (Apache-2.0; Lean 4.32.0; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`) proves planar disk no-retraction/Brouwer and has `invariance_of_domain_open_map` conditional on a `BrouwerFixedPoint E` instance. The repository discharges that instance for its Euclidean plane; it does not own Hatcher’s arbitrary-dimensional U041/U085/U086, nor the arbitrary-dimensional no-retraction clause of U025.
- TauCeti was checked at `T=2db3a983be93975cbf1d54bcc7d6ae1b97830856` (Apache-2.0; Lean 4.34.0-rc2; Mathlib `5fcc6656691ed31965746c369f41fa75e567ac9d`). Its topology stack imports singular-homology/fundamental-group infrastructure but no checked declaration was found for Hurewicz H₁, sphere homology/degree, cellular homology, singular Mayer–Vietoris, Alexander duality, Borsuk–Ulam, simplicial approximation, or Lefschetz fixed point.
- Broad web/GitHub searches on 2026-09-07 found the complete Lean-4 Brouwer package above, but no completed Lean-4 owner for Hurewicz H₁, singular-homology Mayer–Vietoris/cellular homology, Borsuk–Ulam, simplicial approximation, or Lefschetz fixed point. Older Lean-3 sphere-homology/Brouwer developments and theorem statements/placeholders are not credited.
- U087 is deliberately positive: `Real.nonempty_algEquiv_or` proves every algebraic real field extension is ℝ or ℂ. A finite-dimensional commutative unital real division algebra is an algebraic field extension, so the source theorem is a direct specialization of this stronger pinned theorem.
- `N=2026-09-07` denotes a dated unmatched result after the prescribed search layers. Strict whole-row semantics are applied uniformly: specializations, adjacent algebra, isolated clauses/examples, and unbridged alternative representations do not count.

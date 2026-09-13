---
type: reference
title: Provenance contract for FC07 C03
description: '# Provenance contract for FC07 C03'
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
# Provenance contract for FC07 C03

# Provenance contract for FC07 C03

- Canonical source block: FC07 Hatcher, Chapter 3, `FC07-C03-U001`–`FC07-C03-U159`, exactly 159 contiguous rows retrieved from [[foundational-corpus-units-fc07-hatcher|FC07 — Hatcher, Algebraic Topology]] through `agent-memory`.
- Search order followed the mapping plan: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, then pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=633b366493a76df88a2bff099ed0cbf711a59ec9` (Apache-2.0, Lean 4.34.0-rc2), current/open work and indexed searches, Reservoir/package discovery, broad GitHub/discoverable Lean, and local mirrors. No `project-existing` C03 owner was found.
- Every promoted Mathlib declaration/path was compiled through the project toolchain at the exact pin `P`; every cited source path was also verified with `git cat-file` at the pinned git object. C03 therefore uses only `mathlib` and `unmatched` routes: 12 pinned positive rows and 147 dated unmatched rows.
- The exact pinned positives are U002 (abelian dual and precomposition), U003 (dual cochain complex), U004 (projective/free-resolution lift, homotopy uniqueness, and resolution-independent dual cohomology via Ext), U025 (tensor product of abelian groups), U055 (directed systems/direct limits), U073 (right exactness of tensor product), U091 (H-spaces), U100 (Lucas congruence), U108 (SO(n) as determinant-one orthogonal matrices), U126 (inverse limits as compatible sections), U128 (p-adic integers as the inverse limit of `ZMod (p^n)` via the universal property), and U133 (the two six-term Hom/Ext exact sequences).
- `ChainComplex.linearYonedaObj` is the decisive C03 cochain-level interface: over `ModuleCat ℤ` it has degree-n term `Hom(C_n,G)` with differential induced contravariantly from the chain differential. `ProjectiveResolution.lift`, `liftHomotopy`, `homotopyEquiv`, and `isoExt` then own all clauses of U004; generic resolution machinery is not credited for stronger UCT rows without their stated exact sequences/splittings.
- `TensorProduct.gradedMul` and `tmul_of_gradedMul_of_tmul` at P implement the exact Koszul multiplication `(a⊗b)(c⊗d)=(-1)^(|b||c|)ac⊗bd`, but U026 also asserts that the cohomology cross product is a ring homomorphism. Since no checked singular-cohomology cross product exists, strict bundle semantics leave U026 unmatched. Likewise `GradedRing` supplies degree-compatible multiplication but not Hatcher’s graded-commutativity sign clause in U020.
- `Matrix.orthogonalGroup`/`mem_orthogonalGroup_iff` supply the algebraic O(n) characterization, but `TopologicalSpace (Matrix.orthogonalGroup (Fin 2) ℝ)` does not synthesize at P. U107 therefore remains unmatched because its subspace-topology clause is part of the row. `Matrix.specialOrthogonalGroup` and `mem_specialOrthogonalGroup_iff` do own U108, which has no topology clause.
- Current upstream `H=633b366493a76df88a2bff099ed0cbf711a59ec9` was verified as the 2026-09-06 Mathlib dependency-update commit. Current Mathlib code search found no `singularCohomology`, cup-product cohomology, or `PoincareDuality` declaration. The main Chapter-3 topological gap therefore persists beyond P: singular/reduced/relative/cellular cohomology, cup/cap products, compact-support cohomology, Poincaré/Alexander duality, Bockstein, covering-space transfer, and local coefficients are not bridged by checked current interfaces.
- Mathlib does contain substantial algebraic group-cohomology infrastructure (including finite cyclic groups), but U139–U144 are topological cohomology-ring computations of `K(G,1)` spaces and transfer examples. No checked `K(G,1)`/singular-cohomology bridge and no required ring computation were found, so these remain unmatched.
- Generic Čech nerves and sheaf Čech cohomology are not Hatcher’s topological Čech cohomology of open-cover nerves; generic fiber/vector-bundle pullbacks are not bundles of groups with fiberwise group-isomorphism structure; and the algebraic finite-group transfer is not the covering-space transfer. These name-adjacent APIs are not credited.
- A broad external search found no complete Lean-4 owner for the missing Chapter-3 singular-cohomology/duality/local-coefficient interfaces. A small external cohomology-ring development found in discovery is coefficient- and construction-specific and does not own the general Hatcher rows.
- `N=2026-09-07` denotes a dated unmatched result after the prescribed search layers. Strict whole-row semantics are applied uniformly: specializations, adjacent algebra, isolated clauses/examples, and unbridged alternative representations do not count.


---
type: reference
title: Provenance contract for FC08 C03
description: '# Provenance contract for FC08 C03'
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
# Provenance contract for FC08 C03

# Provenance contract for FC08 C03

- Canonical source block: FC08 Lee, Chapter 3, `FC08-C03-U001`–`FC08-C03-U057`, exactly 57 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order followed the Sweep-II plan: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, then pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), followed by current/open/indexed and external Lean checks for the remaining interfaces. No `project-existing`, `package-import`, or `reference-port` C03 owner survived strict bundle checking.
- Every promoted Mathlib path exists at exact `P`. `/tmp/fc08-c03-witness.lean` compiled through the project toolchain and checks the nontrivial U011 assembly: `fdifferential` of the identity is the identity on `PointDerivation`, and for a smooth diffeomorphism the derivation differentials of the map and its inverse are mutual inverses. The same witness checks the `PointDerivation` real-module instance and the smooth-function stalk/evaluation interfaces used in the germ audit. The witness is audit evidence only, not project source.
- C03 has 17 pinned `mathlib` rows and 40 dated `unmatched` rows. Positive rows are: U001, U002, U003, U004, U007, U008, U009, U010, U011, U043, U044, U047, U048, U051, U052, U053, U054.
- The decisive C03 interface boundary is explicit in pinned `Mathlib/Geometry/Manifold/DerivationBundle.lean`: `PointDerivation` formalizes Lee’s algebraic tangent-space definition and `fdifferential` formalizes the differential by precomposition, but the file only documents that this model coincides with the usual tangent space for finite-dimensional `C^∞` real manifolds; it does not provide a checked `PointDerivation ≃ TangentSpace` equivalence. Targeted searches at `P` and current `H` found no such bridge. Consequently U005–U006 and U012–U042 are not inferred from the otherwise extensive chart/model-space `TangentSpace`, `mfderiv`, `TangentBundle`, and `tangentMap` APIs.
- U002–U004 and U007–U011 are promoted entirely inside the derivation model. `PointDerivation` is generic `Derivation` on smooth functions with evaluation at the point as the scalar action; `fdifferential_apply` is literally Lee’s precomposition formula. For U011, chain, identity, and diffeomorphism-inverse clauses were compiled at the pin rather than inferred from the separate standard tangent-space derivative API.
- U001 is independent of the later derivation identification: Mathlib’s standard-model `TangentSpace` is definitionally the model vector space and its constant-fibre `TangentBundle` total space canonically identifies with base × fibre, matching Lee’s preliminary geometric tangent-vector model up to suppression of the fixed base coordinate.
- U043–U044 are mapped to the stalk of the smooth real-function sheaf. `exists_germ_eq`, `germ_eq`, and `germ_res_apply` give exactly the representative/restriction/equality-on-a-neighborhood semantics of smooth germs. U045 remains unmatched because the pin does not package these stalks with the complete scalar-algebra/module structure needed to instantiate Lee’s ℝ-linear point-derivation space on germs; generic `Derivation` plus a stalk is only adjacent infrastructure without that assembly.
- U047–U048 and U051–U054 are direct generic category-theory interfaces. U050 is not promoted from `CategoryTheory.Pointed` alone because Lee’s row deliberately ranges over pointed sets, topological spaces, and smooth manifolds; the checked sources do not package the full pointed-smooth-manifold category. U055–U057 similarly remain unmatched because the specific smooth-manifold categories/functors are not bundled interfaces even though their constituent pointwise maps and functorial laws exist.
- Current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` was checked without changing the pinned worktree. Exact greps for a `PointDerivation`/`TangentSpace` bridge, a tangent functor, velocity realization, coordinate-vector tangent APIs, and a pointed smooth-manifold category found no current-only owner. The project and pinned Mathlib worktrees remained unmodified by the audit.
- `N=2026-09-07` denotes a dated unmatched result after the prescribed search layers. Strict whole-row semantics apply uniformly: no proper subset, unbridged equivalent model, isolated example, or reconstruction of the missing theorem is promoted.


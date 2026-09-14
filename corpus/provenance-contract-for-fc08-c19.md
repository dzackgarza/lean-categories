---
type: reference
title: Provenance contract for FC08 C19
description: '# Provenance contract for FC08 C19'
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
# Provenance contract for FC08 C19

- Canonical source block: FC08 Lee, Chapter 19, `FC08-C19-U001`–`FC08-C19-U037`, exactly 37 unique catalogue rows.
- The 2026-09-14 exact-route remap separates distribution/foliation definitions from the genuinely absent Frobenius/global-leaf/PDE theorems. Current totals are `mathlib` 10, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 27.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`; current upstream was inspected at `H=87befc843c2b3a1be12f7fe9ba274d212b544348`. C10 supplies the direct smooth tangent-subbundle predicate, C05 the immersed-submanifold/tangent data, C08 the manifold Lie bracket, and C14 the form/tensor definitions. Accordingly smooth distributions, integral manifolds, involutivity, integrability, annihilating-form ideals, foliations, and invariance/left-invariance are direct native predicates rather than missing wrappers.
- The local spanning-frame/coframe characterizations remain tied to the still-unmatched C10 smooth-subbundle local-frame criterion. The one-form/Pfaffian criteria additionally require the global manifold exterior derivative still absent in C14. These dependencies are recorded explicitly instead of reclassifying the underlying definitions as greenfield work.
- Exact searches of current Mathlib, TauCeti, and the live formalization corpus found no general Frobenius/foliation API. Thus U019, U020, U022, U023 and U026–U030 remain theorem-level residuals. U021 is promoted separately because its polynomial coordinate change and Lie-bracket calculation directly verify the source example without invoking a missing general theorem.
- The Lie-group tail was checked against TauCeti current `C=35469bdd4baafcaf1da88fba1e6f6d66d623aaac`. `Geometry/Lie/Subgroup/LieAlgebra.lean` explicitly states that the subalgebra↔immersed-Lie-subgroup correspondence (`exists_immersedLieSubgroup_lieSubalgebra`) is a later layer and unavailable there. Hence U032–U034 are not inferred from adjacent exponential/adjoint infrastructure; U034 remains exactly the missing connected subgroup integration theorem.
- The overdetermined PDE results U035–U037 are applications/specializations of Frobenius and no independent proof-complete owners were found. The live `Frobenius theorem` search hits were Mathlib import noise, unrelated algebraic Frobenius material, or a TauCeti roadmap with admitted suggested declarations, not checked implementations.
- Search errors/timeouts are never negative evidence. Every surviving unmatched route is tied to a successful current-source inspection or a precisely named unresolved dependency.

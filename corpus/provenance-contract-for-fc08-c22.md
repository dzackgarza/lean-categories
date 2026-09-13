---
type: reference
title: Provenance contract for FC08 C22
description: '# Provenance contract for FC08 C22'
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
# Provenance contract for FC08 C22

# Provenance contract for FC08 C22

- Canonical block: `FC08-C22-U001`–`FC08-C22-U064`, exactly 64 unique contiguous rows.
- Search order: project `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0; Lean 4.33.0), current `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0; Lean 4.34.0-rc2), current Mathlib documentation, then indexed/current/external Lean search.
- Result: 0 positive routes and 64 dated `unmatched` rows.
- Linear-algebra search found `BilinForm.Nondegenerate`, `BilinForm.finrank_orthogonal`, and `Mathlib.LinearAlgebra.SymplecticGroup` (the canonical matrix symplectic group), but no general symplectic-vector-space structure or checked conversion from Lee’s alternating 2-covector representation. Under strict bundle semantics U001–U011 are not silently recoded through that gap.
- Project search at A found no symplectic/Hamiltonian/Poisson/contact implementation. P/H/current documentation has no manifold symplectic module; the current public Mathlib index exposes the matrix symplectic-group module but no symplectic-manifold/Hamiltonian/contact counterpart.
- U012–U024 also depend on the missing smooth manifold differential-form/exterior-derivative layer identified in FC08 C14–C18. U025–U042 need Hamiltonian/Poisson geometry; U043–U052 contact/Legendrian geometry; U053–U064 the resulting characteristic-flow treatment of nonlinear first-order PDEs. No complete checked owners were found for those layers.
- `N=2026-09-07` marks all negative decisions; strict whole-row semantics apply uniformly.

---
type: reference
title: Foundational corpus mapping FC14 Humphreys
description: '# Foundational corpus mapping FC14 Humphreys'
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
# Foundational corpus mapping FC14 Humphreys

# Foundational corpus mapping FC14 Humphreys

# FC14 — Humphreys, *Introduction to Lie Algebras and Representation Theory* mapping

Status: **Structured definitional residue pass 2 complete 2026-09-17.** The canonical definition index has 176/176 mapped definitions: 110 `mathlib`, 1 `project-existing`, 47 `reference-port`, and 18 scoped `unmatched [negative-search-complete]`. The pass corrected eleven first-pass false negatives caused by theorem-contaminated mixed rows or missing wrapper names; the remaining 18 rows require a genuine construction or intrinsic well-definedness result. They are provisional residue for the later unconstrained prior-art audit, not authorization for Sweep III.

Canonical catalogue: [[foundational-corpus-units-fc14-humphreys|FC14 — Humphreys, Introduction to Lie Algebras and Representation Theory]].

Pinned project baseline: Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0. Current Mathlib checked through `e06e14b71d82002ee32ce854c8ec9ebba95f9627` during the 2026-09-16 first-pass adjudication. Declarations first appearing after the project pin are revision-specific `reference-port` routes unless independently importable.

Every canonical unit receives exactly one Sweep-II route: `mathlib`, `project-existing`, `package-import`, `reference-port`, or `unmatched`. Project source is searched first, followed by pinned/current Mathlib, open/current work, indexed services, Reservoir/packages, broad GitHub Lean repositories, and local reference corpora. The 2026-09-07 records used strict whole-row semantics; the current first-pass definitional Mapping supersedes that rationale row by row with source-clause semantic comparison and expanded current/external searches.

## Structured definitional residue pass 2 — 2026-09-17

The 29 provisional FC14 residues were re-read against Humphreys's exact source clauses and current prerequisites, then re-searched against pinned/current Mathlib, the live Formalization Corpus and current TauCeti material. Fresh searches over the surviving Lie/Jordan/Casimir, exceptional-coordinate, generalized-inner-automorphism/locally-nilpotent, and Harish--Chandra/completed-character clusters produced no new proof-complete owner. Current Mathlib's `Algebra/Lie/BaseChange.lean` was also inspected declaration-by-declaration and supplies the fully general Lie structure on `A ⊗[R] L`, which closes the definitional part of the arbitrary-field Chevalley-algebra row.

Eleven first-pass negatives were dependency or wrapper artifacts under the definition-only policy. The arbitrary-subset centralizer is the displayed native commuting-set predicate; `Aut(L)` is the existing self-`LieEquiv` carrier with identity/composition/inverse; and `Int(L)` is generated-subgroup closure of the already-routed nilpotent-adjoint exponentials. Weyl chambers/fundamental chambers are native connected-component/strict-halfspace constructions. TauCeti already gives proof-complete source constructions for the classical A/B/C/D root systems, while their symmetric/signed-permutation Weyl-group descriptions are theorem clauses. Saturation/highest-weight is a literal predicate on the weight lattice. Humphreys's `M_λ` is a direct full subcategory of the project-owned `LieModuleCat` once the separately catalogued infinite-support character carrier is supplied. Finally, `L(K)=K ⊗[ℤ] L(ℤ)` is exactly Mathlib's native Lie extension of scalars. No definition authoring occurred.

The 18 survivors are construction-bearing: the coefficient-to-Lie-algebra converse for structure constants; lifting ordinary Jordan components back inside a semisimple Lie algebra; the nonfaithful Casimir reduction; recursive root recovery from a Cartan matrix; Humphreys's full E6/E7/E8 and F4 Euclidean coordinate realizations; the regular-semisimple centralizer/maximal-toral bridge; `E(L)` and relative `E(L;K)` from generalized eigenvectors; source-faithful Cartan/root rank identification; the explicit tensor-algebra existence model; locally nilpotent exponentials; the 14-dimensional `G₂⊂o(7)` model; the full Cayley derivation construction; Harish--Chandra projection/homomorphism with its intrinsic laws; the infinite cone-supported convolution algebra; the Appendix unitriangular character inversion route; and a source monomial carrier on which Kostant height is defined. These remain provisional `[negative-search-complete]` rows for the final open-ended audit.

[Provenance contract for FC14 C01](provenance-contract-for-fc14-c01)

[Chapter I. Basic Concepts FC14](chapter-i-basic-concepts-fc14)


[Provenance contract for FC14 C02](provenance-contract-for-fc14-c02)

[Chapter II. Semisimple Lie Algebras FC14](chapter-ii-semisimple-lie-algebras-fc14)

[Provenance contract for FC14 C03](provenance-contract-for-fc14-c03)

[Chapter III. Root Systems FC14](chapter-iii-root-systems-fc14)

[Provenance contract for FC14 C04](provenance-contract-for-fc14-c04)

[Chapter IV. Isomorphism and Conjugacy Theorems FC14](chapter-iv-isomorphism-and-conjugacy-theorems-fc14)

[Provenance contract for FC14 C05](provenance-contract-for-fc14-c05)

[Chapter V. Existence Theorem FC14](chapter-v-existence-theorem-fc14)

[Provenance contract for FC14 C06](provenance-contract-for-fc14-c06)

[Chapter VI. Representation Theory FC14](chapter-vi-representation-theory-fc14)

[Provenance contract for FC14 C07](provenance-contract-for-fc14-c07)

[Chapter VII. Chevalley Algebras and Groups FC14](chapter-vii-chevalley-algebras-and-groups-fc14)

---
type: reference
title: Foundational corpus mapping FC12 Beauville
description: '# Foundational corpus mapping FC12 Beauville'
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
# Foundational corpus mapping FC12 Beauville

# Foundational corpus mapping FC12 Beauville

# Foundational corpus mapping FC12 Beauville

# Foundational corpus mapping FC12 Beauville

# Foundational corpus mapping FC12 Beauville

# Foundational corpus mapping FC12 Beauville

# Foundational corpus mapping FC12 Beauville

# Foundational corpus mapping FC12 Beauville

# Foundational corpus mapping FC12 Beauville

# Foundational corpus mapping FC12 Beauville

# Foundational corpus mapping FC12 Beauville

# Foundational corpus mapping FC12 Beauville

# Foundational corpus mapping FC12 Beauville

# FC12 — Beauville, *Complex Algebraic Surfaces*, 2nd ed. mapping

Status: **Structured definitional residue pass 2 complete 2026-09-17.** All 45 FC12 definitional obligations have source-clause semantic adjudication: 12 route to generic/pinned Mathlib constructions, 4 route to existing canonical project owners, and 29 remain scoped `unmatched [negative-search-complete]`. The 29 negatives are provisional State-1 residue for the later unconstrained prior-art audit; they do not authorize Sweep III. The regenerated definition index contains no FC12 first-pass `search` or `review` action.

Canonical catalogue: [[foundational-corpus-units-fc12-beauville|FC12 — Beauville, Complex Algebraic Surfaces, 2nd ed.]].

Pinned project baseline: Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0. Current Mathlib checked through `fd634dd29761b5d32af50e2b8f6d8ad043024303` during the 2026-09-15 first-pass adjudication. Declarations first appearing after the project pin are revision-specific `reference-port` routes unless independently importable.

Every canonical unit receives exactly one Sweep-II route: `mathlib`, `project-existing`, `package-import`, `reference-port`, or `unmatched`. Project source is searched first, followed by pinned/current Mathlib, open/current work, indexed search services, Reservoir/packages, broad GitHub Lean discovery, and local reference corpora. The 2026-09-07 records used strict-bundle semantics; current first-pass definitional Mapping supersedes that rationale row by row with source-faithful semantic comparisons and current proof-assistant search evidence.

## Structured definitional residue pass 2 — 2026-09-17

The 40 provisional first-pass residues were re-read against their exact Beauville source clauses and catalogue prerequisites, then re-searched in surface-intersection, birational/blow-up, linear-system/projective-bundle, Albanese/quotient-surface, K3/Enriques/elliptic, positive-characteristic and compact-complex-surface batches. Fresh live-corpus searches remained negative for the construction-heavy surface geometry, and a current-upstream Mathlib/GitHub check still found only object-level `Scheme.Birational`/`PartialIso`, not a predicate that a specified scheme morphism is birational. Accordingly the point-blowup, birational-domination/minimality, relative projective-bundle, Albanese, quotient-surface, double-cover and related geometric constructors remain residue.

Eleven first-pass negatives were instead dependency-accounting errors under the definition-only policy already applied in FC08/FC11. The pass now routes the Néron--Severi image/restricted-form construction, standard numerical invariants, Hirzebruch notation, Kodaira dimension, Beauville's Enriques and K3 predicates, elliptic-surface predicate, the definition-only parts of the positive-characteristic K3/quasi-elliptic/non-classical-Enriques rows, and compact-surface `h,b⁺,b⁻` notation to native generic constructions. These rows introduce only images/restrictions, dimensions/signatures, suprema/maxima, conjunctions, existential predicates or terminology once their separately catalogued geometric inputs exist. Missing geometric carriers and all mixed-row comparison/classification assertions remain at their own upstream or Sweep-IV obligations rather than being duplicated as new definitions. No definition authoring occurred.

## State-2 FC12 tail recheck — 2026-09-25

At repository HEAD `ab1b346823b780e7688b6a020bd58cb375e56da6`, the live definition selector has
16 FC12 rows with `action != reuse`:
`C01-U008`, `C01-U012`, `C02-U005`, `C02-U006`, `C03-U015`,
`C04-U003`, `C04-U005`, `C04-U006`, `C04-U007`, `C04-U008`,
`C04-U011`, `C04-U013`, `C04-U014`, `C08-U024`, `B-U006`, and
`B-U007`. Each blocker was re-evaluated against the owners landed since the
earlier FC12 audit. None is dependency-ready for a source-faithful Sweep-III
construction.

- `C01-U008` is not discharged by
  `Topology/FourManifoldIntersectionData.lean`: that owner constructs the
  integral cup-product intersection form on `H²/tors`, whereas Beauville's
  notation is the divisor/Picard intersection pairing. The missing bridge is
  exactly the geometric `c₁ : Pic(S) → H²(S,ℤ)` package in `C01-U012`.
  `SurfaceGysinData` likewise supplies a wrong-way map on integral
  cohomology and does not construct this divisor-class map. `C01-U012`
  therefore remains blocked at the analytic exponential sequence, integral
  first Chern map, and its Picard/Néron--Severi comparison.
- `C02-U005` was rechecked after
  `Schemes/CompleteLinearSystemData.lean` landed. That owner gives exactly
  the complete carrier `|D|={D'≥0 | D'~D}`, but Beauville additionally
  defines a linear system as a projective linear subspace and then defines
  pencils, fixed components/fixed part, and base points inside that projective
  system. The repository still has no source-faithful projective-linear-system
  structure or section/projectivization comparison on this carrier; replacing
  it by an arbitrary family of divisors would be a surrogate. `C02-U006`
  remains a correspondence/result row downstream of this missing structure.
- `C03-U015` still lacks the construction assigning a line-bundle extension
  its class in `H¹(C,L⊗M⁻¹)`. Abstract Ext/sheaf-cohomology infrastructure
  does not supply the required `Ext¹(M,L) ≃ H¹(C,L⊗M⁻¹)` specialization;
  choosing an arbitrary cohomology class would change the construction.
- The rational-surface tail remains non-executable in Sweep III. `C04-U003`
  and `C04-U005` still require the missing `C02-U005` projective linear
  system/base-condition structure; `PointBlowupData` supplies an exact
  proof-free candidate graph for a point blow-up but not existence of the
  blow-up or the exceptional Picard/intersection calculus used by
  `C04-U005` and `C04-U007`. `C04-U006` and `C04-U008` are
  point/tangent-separation and subsystem/projection comparison statements.
  `C04-U011` and `C04-U013` are Veronese/Steiner examples whose missing
  clauses are embedding, degree, image, and singularity results. The landed
  relative-projective-bundle and Hirzebruch carriers remove the old carrier
  gap from `C04-U014`, but the `|h+f|` embedding and projected-Veronese
  identification remain result content; the current Hirzebruch owner also
  explicitly lacks the quotient-induced negative section.
- `C08-U024` still has no proof-complete global construction gluing the
  affine square-root charts attached to an arbitrary order-two line bundle;
  the available affine étale square-root prior art and generic torsor
  infrastructure do not produce Beauville's global cover or the pullback
  trivialization without the missing gluing results.
- `B-U006` still lacks the compact-complex analytic quotient
  `L* / q^ℤ` of a punctured nonzero-degree holomorphic line bundle, including
  the properly discontinuous holomorphic quotient construction. Consequently
  `B-U007` also remains blocked: its finite free quotient must live in the
  compact-complex-analytic category, not merely as a topological or algebraic
  quotient.

Accordingly this recheck lands no new FC12 Lean declaration: every surviving
row would require either a missing geometric constructor or theorem/result
work forbidden by the Sweep-III phase boundary.

[Provenance contract for FC12 C01](provenance-contract-for-fc12-c01)

[Chapter I. Generalities on Algebraic Surfaces FC12](chapter-i-generalities-on-algebraic-surfaces-fc12)

[Provenance contract for FC12 C02](provenance-contract-for-fc12-c02)

[Chapter II. Birational Maps and Blow-ups FC12](chapter-ii-birational-maps-and-blow-ups-fc12)

[Provenance contract for FC12 C03](provenance-contract-for-fc12-c03)

[Chapter III. Ruled Surfaces FC12](chapter-iii-ruled-surfaces-fc12)

[Provenance contract for FC12 C04](provenance-contract-for-fc12-c04)

[Chapter IV. Rational Surfaces FC12](chapter-iv-rational-surfaces-fc12)

[Provenance contract for FC12 C05](provenance-contract-for-fc12-c05)

[Chapter V. The Albanese Map and Rationality FC12](chapter-v-the-albanese-map-and-rationality-fc12)

[Provenance contract for FC12 C06](provenance-contract-for-fc12-c06)

[Chapter VI FC12](chapter-vi-fc12)

[Provenance contract for FC12 C07](provenance-contract-for-fc12-c07)

[Chapter VII. Kodaira Dimension FC12](chapter-vii-kodaira-dimension-fc12)

[Provenance contract for FC12 C08](provenance-contract-for-fc12-c08)

[Chapter VIII. Surfaces of Kodaira Dimension Zero FC12](chapter-viii-surfaces-of-kodaira-dimension-zero-fc12)

[Provenance contract for FC12 C09](provenance-contract-for-fc12-c09)

[Chapter IX. Elliptic Surfaces FC12](chapter-ix-elliptic-surfaces-fc12)

[Provenance contract for FC12 C10](provenance-contract-for-fc12-c10)

[Chapter X. Surfaces of General Type FC12](chapter-x-surfaces-of-general-type-fc12)

[Provenance contract for FC12 A](provenance-contract-for-fc12-a)

[Appendix A. Surfaces in Positive Characteristic FC12](appendix-a-surfaces-in-positive-characteristic-fc12)

[Provenance contract for FC12 B](provenance-contract-for-fc12-b)

[Appendix B. Compact Complex Surfaces FC12](appendix-b-compact-complex-surfaces-fc12)

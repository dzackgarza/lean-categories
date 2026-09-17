---
type: reference
title: Foundational corpus mapping FC06 Hartshorne
description: '# Foundational corpus mapping FC06 Hartshorne'
tags:
- project
- reference
timestamp: '2026-09-06T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# Foundational corpus mapping FC06 Hartshorne

# Foundational corpus mapping FC06 Hartshorne

# FC06 — Hartshorne, *Algebraic Geometry* mapping

Status: **Sweep II complete.** C01–C05 are complete.

Canonical catalogue: [[foundational-corpus-units-fc06-hartshorne|FC06 — Hartshorne, Algebraic Geometry]].

Pinned project baseline: Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0. Current Mathlib was refreshed 2026-09-06 to `5aedf732b6987e8c26ab3c9ebc855314f82b045f`; declarations first appearing after the project pin are revision-specific reference-port routes unless an importable package route is independently justified.

Every canonical unit receives exactly one Sweep-II route: `mathlib`, `project-existing`, `package-import`, `reference-port`, or `unmatched`. Project source is searched first, followed by pinned/current Mathlib, open/current work, indexed search services, and relevant external Lean repositories. Strict bundle semantics apply throughout.

## Structured definitional residue pass 2 — 2026-09-16

The 75 FC06 provisional definitional residues were re-searched in chapter/topic batches against pinned/current Mathlib, the live Formalization Corpus, and current algebraic-geometry work in Atlas, Clawristotle, the Jacobian projects, AINTLIB, and related repositories. The pass revisited birational maps and blowups; Proj modules, twists, relative Proj/projective bundles, Cartier divisors and linear systems; differentials, smooth relative dimension, formal schemes and formal functions; curves, Frobenius, Picard/Jacobian and hyperelliptic constructions; and the surface/intersection/Kodaira block.

No canonical definitional route changed. Several new candidates are useful prior art but fail the source contract on carrier, generality, or proof completeness. Current Atlas `BlowupAtPoint.lean` is `sorry`-free and defines the Rees–Proj blowup together with the closure-off-center proper transform, but Hartshorne C01-U083 is the explicit incidence subscheme in `A^n × P^(n-1)` and no checked comparison identifying the two models was found; Atlas `BlowupDefinition.lean` itself still contains proof holes. Atlas `CartierDivisorScheme.lean` is `sorry`-free but assumes an integral scheme and uses its function field, so it is narrower than Hartshorne's arbitrary-scheme `K*/O*` definition. Atlas `TwistingSheaves.lean` names the correct Proj twist, but depends on `Lec14QCohProjective.lean`, whose `GrMod.shift` and `tildeProj` are still `sorry`; its auxiliary line-bundle/global-section theorems also contain `sorry`. Atlas Kähler-differential material is ring-level or proof-incomplete and does not supply Hartshorne's sheaf `Omega_{X/Y}` from the diagonal ideal. Pinned Mathlib's `SmoothOfRelativeDimension` is a checked modern local-standard-smooth predicate, but no checked theorem identifies it with Hartshorne's exact flatness/component-dimension/differential-rank definition, so C03-U152 cannot be accepted by name alone. Searches for an absolute scheme Frobenius, formal schemes/`Spf`, source-shaped relative Proj, Kodaira dimension, the Hartshorne Picard/Jacobian interfaces, and the abstract degree-two hyperelliptic definition did not produce a checked source-complete implementation. Equation-specific hyperelliptic/Jacobian projects and Hasse/isogeny roadmaps use different carriers or contain explicit `sorry`, and therefore were not promoted.

All 75 rows remain scoped `unmatched [negative-search-complete]` residue for the later unconstrained open-ended audit. The clean Atlas proper-transform and Cartier-specialization files are recorded here as positive partial evidence so that final search need not rediscover them; zero-hit topic searches were not treated as authorization to author definitions.

[Provenance contract for FC06 C01](provenance-contract-for-fc06-c01)

[Chapter 1. Varieties FC06](chapter-1-varieties-fc06)

[Provenance contract for FC06 C02](provenance-contract-for-fc06-c02)

[Chapter 2. Schemes FC06](chapter-2-schemes-fc06)

[Provenance contract for FC06 C03](provenance-contract-for-fc06-c03)

[Chapter 3. Cohomology FC06](chapter-3-cohomology-fc06)

[Provenance contract for FC06 C04](provenance-contract-for-fc06-c04)

[Chapter 4. Curves FC06](chapter-4-curves-fc06)

[Provenance contract for FC06 C05](provenance-contract-for-fc06-c05)

[Chapter 5. Surfaces FC06](chapter-5-surfaces-fc06)

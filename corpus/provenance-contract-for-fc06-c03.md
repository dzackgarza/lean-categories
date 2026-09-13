---
type: reference
title: Provenance contract for FC06 C03
description: '# Provenance contract for FC06 C03'
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
# Provenance contract for FC06 C03

# Provenance contract for FC06 C03

## Provenance contract for FC06 C03

- Canonical source block: FC06 Hartshorne, Chapter III, `FC06-C03-U001`–`FC06-C03-U204`, in canonical source-ID order. C01–C02 were already promoted and were not modified.
- Project-first inspection is recorded against `A=cd74b69e97f743cd7318a9fe130ed2a749860b3f`; repository HEAD `3b2239e161592472b34e02ad3b7da308f9ce7280` changes only `TODO.md`. Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0. Current Mathlib was refreshed at `H=5aedf732b6987e8c26ab3c9ebc855314f82b045f`, Lean 4.34.0-rc2.
- The pre-existing project source atlas and Hartshorne definition catalogue were reused before new discovery. Targeted P/H exact-declaration checks then resolved derived functors, sheaf cohomology, Čech complexes, flatness, projective dimension and semicontinuity. Open Mathlib PR and indexed GitHub searches were run for Serre duality, higher direct images, formal functions, semicontinuity/cohomology base change, Stein factorization, generic smoothness and Bertini; no additional complete route was verified.
- Strict bundle semantics govern every row. A route must own the complete source statement; partial clauses, analogous interfaces, stronger hypotheses, and declarations whose proof is `sorry` are not promoted.
- Clawristotle `coherent-cohomology-finite` at `C=09497ebf6ee48ef49c4f3d24501954bc3a2855d6` is Apache-2.0, Lean 4.32.0-rc1, Mathlib `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` and therefore reference-only relative to P. Its axiom-clean `AcyclicResolution.lean` exactly supplies U015 (`Functor.IsRightAcyclic`) and U016 (`rightDerivedIsoOfAcyclicResolution`), which are recorded as `reference-port`.
- The recorded Atlas files `AffinePushforwardHigher.lean` and `AffinePushforwardCohomology.lean` at local Atlas revision `34ffed396f376454c1a9b297f3fd74c5c801fb50` contain matching affine-pushforward statements but their substantive theorems use `by sorry`; they are statement-bank evidence only and are not mapping routes. Their noncommercial/no-training license would in any case require separate handling before any port.
- Pinned Mathlib contains generic sheaf cohomology and a Čech-complex construction, but not the affine/projective coherent-cohomology comparison and finiteness theorems required by Hartshorne III.2–III.5. It contains global Ext/projective-dimension infrastructure, but not the internal sheaf-Ext/Serre-duality programme. The regular-sequence source explicitly lists Koszul regular sequences as TODO, so U095–U096 remain unmatched.
- Flatness primitives U119/U121/U122/U123 have direct pinned owners. Smooth/étale infrastructure exists, but it is not credited to Hartshorne’s differently bundled smoothness definition or the major geometric generic-smoothness/Bertini assertions without checked equivalence theorems.
- No checked P/H/open/external implementation was found for Hartshorne’s formal-functions theorem, coherent higher-direct-image finiteness, semicontinuity theorem for proper families, cohomology-and-base-change theorem, or Stein factorization. Generic `UpperSemicontinuous` and its closed-superlevel characterization do exactly own U195–U196.
- `N=2026-09-06` marks a dated unmatched decision after project-first, P, H/current, recorded open/current work, indexed search services and relevant external Lean checks.


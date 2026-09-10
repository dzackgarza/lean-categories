---
title: "Coverage"
---

Every definition, theorem, lemma, example and remark in a read chapter is a
numbered unit. A swept chapter assigns each of its units exactly one route: a
Lean declaration that owns the whole statement, or a finding that nothing does.

Routes are strict about bundles. A unit is credited only when a checked
declaration carries the statement the source makes, hypotheses included. A
partial match is recorded as unmatched, with the partial named in its entry.

| Source | Units | Swept | In Lean | Not in Lean |
| --- | ---: | ---: | ---: | ---: |
| [FC01 — Dummit & Foote, *Abstract Algebra*](sources/fc01/) | 13 | 0/1 | — | — |
| [FC03 — Riehl, *Category Theory in Context*](sources/fc03/) | 434 | 0/7 | — | — |
| [FC04 — Atiyah & Macdonald, *Introduction to Commutative Algebra*](sources/fc04/) | 433 | 10/11 | 246 | 90 |
| [FC05 — Weibel, *An Introduction to Homological Algebra*](sources/fc05/) | 1059 | 11/11 | 288 | 771 |
| [FC06 — Hartshorne, *Algebraic Geometry*](sources/fc06/) | 969 | 5/5 | 140 | 829 |
| [FC07 — Hatcher, *Algebraic Topology*](sources/fc07/) | 612 | 6/6 | 102 | 510 |
| [FC08 — Lee, *Introduction to Smooth Manifolds*](sources/fc08/) | 1405 | 26/26 | 323 | 1082 |
| [FC09 — Neukirch, *Algebraic Number Theory*](sources/fc09/) | 803 | 7/7 | 168 | 635 |
| [FC10 — Serre, *Local Fields*](sources/fc10/) | 636 | 15/15 | 103 | 533 |
| [FC11 — Peters & Sterk, *Symmetric and Quadratic Forms*](sources/fc11/) | 1114 | 3/24 | 55 | 154 |
| [FC12 — Beauville, *Complex Algebraic Surfaces*](sources/fc12/) | 206 | 12/12 | 0 | 206 |
| [FC13 — Matsumura, *Commutative Ring Theory*](sources/fc13/) | 740 | 12/15 | 234 | 438 |
| [FC14 — Humphreys, *Introduction to Lie Algebras and Representation Theory*](sources/fc14/) | 384 | 1/7 | 31 | 21 |
| [FC15 — Humphreys, *Reflection Groups and Coxeter Groups*](sources/fc15/) | 304 | 0/8 | — | — |
| [FC16 — Humphreys, *Linear Algebraic Groups*](sources/fc16/) | 468 | 0/12 | — | — |

## Across every swept chapter

| Route | Units | Share | Meaning |
| --- | ---: | ---: | --- |
| [`unmatched`]{.route-unmatched} | 5269 | 76% | No checked Lean owner was found. |
| [`mathlib`]{.route-mathlib} | 1503 | 22% | Mathlib owns the unit outright. |
| [`reference-port`]{.route-reference-port} | 110 | 2% | An external Lean development owns it and is ported with provenance. |
| [`project-existing`]{.route-project-existing} | 72 | 1% | This repository already owns it. |
| [`package-import`]{.route-package-import} | 4 | 0% | A Lake-packaged library owns it. |
| [`x\`]{.route-x\} | 1 | 0% |  |
| **total** | **6959** | | |

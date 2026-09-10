---
title: "Coverage"
---

The corpus is a fixed list of graduate textbooks, read cover to cover. Every
definition, theorem, lemma, example and remark in a swept chapter becomes a
numbered *unit*, and every unit is assigned exactly one route: a Lean declaration
that owns it, or a finding that nothing does.

Routes are strict about bundles. A unit is credited only when a checked declaration
carries the whole statement the source makes, hypotheses included. A partial match
is recorded as unmatched, with the partial named in its row.

## Every source

| Source | Units | Mathlib | Owned here | Ported | Unmatched |
| --- | ---: | ---: | ---: | ---: | ---: |
| [FC04 — Atiyah & Macdonald, *Introduction to Commutative Algebra*](sources/fc04/) | 336 | 223 | 17 | 6 | 90 |
| [FC05 — Weibel, *An Introduction to Homological Algebra*](sources/fc05/) | 1059 | 266 | 4 | 18 | 771 |
| [FC06 — Hartshorne, *Algebraic Geometry*](sources/fc06/) | 969 | 137 | 1 | 2 | 829 |
| [FC07 — Hatcher, *Algebraic Topology*](sources/fc07/) | 612 | 82 | 0 | 20 | 510 |
| [FC08 — Lee, *Introduction to Smooth Manifolds*](sources/fc08/) | 1405 | 323 | 0 | 0 | 1082 |
| [FC09 — Neukirch, *Algebraic Number Theory*](sources/fc09/) | 802 | 151 | 4 | 12 | 635 |
| [FC10 — Serre, *Local Fields*](sources/fc10/) | 636 | 85 | 2 | 16 | 533 |
| [FC11 — Peters & Sterk, *Symmetric and Quadratic Forms*](sources/fc11/) | 209 | 10 | 40 | 5 | 154 |
| [FC12 — Beauville, *Complex Algebraic Surfaces*](sources/fc12/) | 206 | 0 | 0 | 0 | 206 |
| [FC13 — Matsumura, *Commutative Ring Theory*](sources/fc13/) | 672 | 197 | 4 | 33 | 438 |
| [FC14 — Humphreys, *Introduction to Lie Algebras and Representation Theory*](sources/fc14/) | 52 | 29 | 0 | 2 | 21 |

## In total

| Route | Units | Share | Meaning |
| --- | ---: | ---: | --- |
| `unmatched` | 5269 | 76% | No checked Lean owner was found. |
| `mathlib` | 1503 | 22% | Mathlib owns the unit outright. |
| `reference-port` | 110 | 2% | An external Lean development owns it and is ported with provenance. |
| `project-existing` | 72 | 1% | This repository already owns it. |
| `package-import` | 4 | 0% | A Lake-packaged library owns it. |
| **total** | **6958** | | |

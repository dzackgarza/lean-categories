---
title: "Every book"
---

Every definition, theorem, lemma, example and remark in these books is recorded
with its statement and the page it appears on. Where a chapter has been checked
against Lean, each of its statements also says whether some Lean development
already states and proves it.

A statement counts as formalized only when a Lean declaration carries the whole
thing, hypotheses included. Where Lean has part of it, that counts as not
formalized, and the entry names the part that does exist.

| Book | Statements | Checked | Formalized | Not formalized |
| --- | ---: | ---: | ---: | ---: |
| [FC01 — Dummit & Foote, *Abstract Algebra*](sources/fc01/) | 13 | 0 | — | — |
| [FC03 — Riehl, *Category Theory in Context*](sources/fc03/) | 434 | 0 | — | — |
| [FC04 — Atiyah & Macdonald, *Introduction to Commutative Algebra*](sources/fc04/) | 433 | 336 | 246 | 90 |
| [FC05 — Weibel, *An Introduction to Homological Algebra*](sources/fc05/) | 1,059 | 1,059 | 288 | 771 |
| [FC06 — Hartshorne, *Algebraic Geometry*](sources/fc06/) | 969 | 969 | 140 | 829 |
| [FC07 — Hatcher, *Algebraic Topology*](sources/fc07/) | 612 | 612 | 102 | 510 |
| [FC08 — Lee, *Introduction to Smooth Manifolds*](sources/fc08/) | 1,405 | 1,405 | 323 | 1082 |
| [FC09 — Neukirch, *Algebraic Number Theory*](sources/fc09/) | 803 | 803 | 168 | 635 |
| [FC10 — Serre, *Local Fields*](sources/fc10/) | 636 | 636 | 103 | 533 |
| [FC11 — Peters & Sterk, *Symmetric and Quadratic Forms*](sources/fc11/) | 1,114 | 209 | 55 | 154 |
| [FC12 — Beauville, *Complex Algebraic Surfaces*](sources/fc12/) | 206 | 206 | 0 | 206 |
| [FC13 — Matsumura, *Commutative Ring Theory*](sources/fc13/) | 740 | 672 | 234 | 438 |
| [FC14 — Humphreys, *Introduction to Lie Algebras and Representation Theory*](sources/fc14/) | 384 | 52 | 31 | 21 |
| [FC15 — Humphreys, *Reflection Groups and Coxeter Groups*](sources/fc15/) | 304 | 0 | — | — |
| [FC16 — Humphreys, *Linear Algebraic Groups*](sources/fc16/) | 468 | 0 | — | — |

## What the books contain

| Kind of statement | Count |
| --- | ---: |
| Definitions | 2,701 |
| Theorems | 1,228 |
| Propositions | 1,478 |
| Lemmas | 703 |
| Corollaries | 811 |
| Examples | 1,137 |
| Counterexamples | 15 |
| Constructions | 520 |
| Remarks | 260 |
| Conventions | 270 |
| Notations | 18 |
| Formulas | 16 |
| Criteria | 15 |
| Other statements | 408 |
| **Total** | **9,580** |

## Where the checked statements stand

| Status | Statements | Share | What it means |
| --- | ---: | ---: | --- |
| [not formalized]{.route-unmatched} | 5269 | 76% | A documented search found no Lean statement of it anywhere. |
| [in Mathlib]{.route-mathlib} | 1504 | 22% | Mathlib states and proves it. |
| [in another Lean project]{.route-reference-port} | 110 | 2% | Some other Lean development has it; using it means porting that code. |
| [in lean-categories]{.route-project-existing} | 72 | 1% | This repository states and proves it. |
| [in a Lean package]{.route-package-import} | 4 | 0% | A library available as a Lake dependency has it. |
| **checked in total** | **6959** | | |

---
title: "The foundational corpus"
---


Sixteen standard graduate mathematics textbooks, read cover to cover. Every
definition, theorem, lemma, example and remark is recorded as a numbered unit
carrying its statement and the page it appears on — **9,580 of them so far** —
and where a chapter has been swept, each unit also names the Lean declaration
that owns it, or records that none does.

Read a chapter and you get the mathematics of that chapter with the state of its
formalization attached, statement by statement. Every declaration name links to
its Mathlib documentation; every commit and pull request links to the code it
names.

| | |
| --- | ---: |
| Source units enumerated | **9,580** |
| Of those, routed against Lean | 6,959 |
| Owned by Mathlib | 1,503 |
| Owned by an external Lean development | 114 |
| Owned by this repository | 72 |
| **No Lean owner found** | **5,269** |

An unmatched unit is the interesting case: its entry names the partial machinery
that does exist and the gap that stops it closing the statement, so it reads as a
concrete formalization target rather than an absence.

## Where to start

- [Coverage](coverage.md) — every source and how far it has been taken.
- [The corpus](corpus.md) — which books, which editions, what scope, and the
  prerequisite order they are read in.
- [Sweep status](status.md) — the per-source progress table.
- [Definition catalogues](catalogues/) — what each book defines, before any
  question of Lean.

## What the routes mean

| Route | Units | Share | Meaning |
| --- | ---: | ---: | --- |
| [`unmatched`]{.route-unmatched} | 5269 | 76% | No checked Lean owner was found. |
| [`mathlib`]{.route-mathlib} | 1503 | 22% | Mathlib owns the unit outright. |
| [`reference-port`]{.route-reference-port} | 110 | 2% | An external Lean development owns it and is ported with provenance. |
| [`project-existing`]{.route-project-existing} | 72 | 1% | This repository already owns it. |
| [`package-import`]{.route-package-import} | 4 | 0% | A Lake-packaged library owns it. |
| [`x\`]{.route-x\} | 1 | 0% |  |
| **total** | **6959** | | |

## Caveats

The sweep is a search, not a proof. An unmatched unit asserts that a documented
search found no owner on the revisions named in its entry — not that none exists.
Mathlib moves; an entry is only as current as the commits its chapter records.
Statements are compressed restatements of the source, not quotations, and where
one of them and the Lean disagree, the Lean is right.


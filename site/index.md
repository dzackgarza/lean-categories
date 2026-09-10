---
title: "The foundational corpus"
---

This site publishes a unit-by-unit survey of what standard graduate mathematics
textbooks state, and which Lean declaration — if any — already owns each
statement. The corpus fixes 16 books; 11 of them have been swept so far.

It exists because `lean-categories` authors as little Lean as possible. Before
anything is written here, the reuse gate asks whether Mathlib, a packaged
library, or an external development already proves it. The survey is the
accumulated answer, and its unmatched rows are the roadmap.

## What is in it

| | |
| --- | ---: |
| Source units read and routed | **6,958** |
| Owned by Mathlib | 1,503 |
| Owned by an external Lean development | 114 |
| Owned by this repository | 72 |
| **No Lean owner found** | **5,269** |

Every row names the declarations it compared against, at a pinned Mathlib
commit, and says in prose how the interfaces differ. Unmatched rows name the
partial machinery that exists and the gap that stops it closing the statement,
so each one reads as a concrete formalization target.

## Where to start

- [Coverage](coverage.qmd) — the table above, broken out by source and chapter.
- [The corpus](corpus.qmd) — which books, which editions, what scope, and the
  prerequisite order they are read in.
- [Sweep status](status.qmd) — how far each source has been taken.
- [Definition catalogues](catalogues/) — every definition in a source, with its
  page reference.

## How to read a row

The route says who owns the unit:

| Route | Units | Share | Meaning |
| --- | ---: | ---: | --- |
| `unmatched` | 5269 | 76% | No checked Lean owner was found. |
| `mathlib` | 1503 | 22% | Mathlib owns the unit outright. |
| `reference-port` | 110 | 2% | An external Lean development owns it and is ported with provenance. |
| `project-existing` | 72 | 1% | This repository already owns it. |
| `package-import` | 4 | 0% | A Lake-packaged library owns it. |
| **total** | **6958** | | |

## Caveats

The survey is a search, not a proof. An unmatched row asserts that a documented
search found no owner on the pinned revisions it names — not that none exists.
Mathlib moves; a row is only as current as the commits in its provenance note.
Where a claim here and the Lean disagree, the Lean is right.

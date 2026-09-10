---
title: "Graduate mathematics, and what Lean has of it"
---


Sixteen standard graduate mathematics textbooks — Hartshorne, Weibel, Lee,
Neukirch, Serre, Matsumura and others — read cover to cover. Every definition,
theorem, lemma, example and remark in them is written down with its statement and
the page it appears on: **2,701 definitions,
2,706 theorems and propositions,
1,514 lemmas and corollaries**, and
2,659
examples, constructions, remarks and conventions besides.

For 6,959 of those statements someone has then gone looking for the same
statement in Lean, and recorded what they found:

| | |
| --- | ---: |
| Already in Mathlib | 1,504 |
| In some other Lean development | 114 |
| In this repository | 72 |
| **Nowhere in Lean, as far as a documented search could tell** | **5,269** |

That last row is what the site is for. Each of those entries names the pieces
Lean does have and the gap that stops them adding up to the statement, so it
reads as a description of work to be done rather than a blank.

Open a chapter and you get its mathematics in order, each statement with its
location in the book and, where it has been checked, its standing in Lean. Every
declaration name links to its Mathlib documentation; every commit and pull
request links to the code.

## Where to start

- [Every book](coverage.md) — what each one contains and how far it has been checked.
- [The reading list](corpus.md) — which books, which editions, and the order they
  are read in.
- [Progress](status.md) — which chapters have been checked.
- [Definition catalogues](catalogues/) — what each book defines, listed by chapter.

## What the statuses mean

| Status | Statements | Share | What it means |
| --- | ---: | ---: | --- |
| [not formalized]{.route-unmatched} | 5269 | 76% | A documented search found no Lean statement of it anywhere. |
| [in Mathlib]{.route-mathlib} | 1504 | 22% | Mathlib states and proves it. |
| [in another Lean project]{.route-reference-port} | 110 | 2% | Some other Lean development has it; using it means porting that code. |
| [in lean-categories]{.route-project-existing} | 72 | 1% | This repository states and proves it. |
| [in a Lean package]{.route-package-import} | 4 | 0% | A library available as a Lake dependency has it. |
| **checked in total** | **6959** | | |

## What this is not

Checking is a search, not a proof. "Nowhere in Lean" means a documented search of
Mathlib at a named commit, of open pull requests, and of the Lean developments
its entry names, turned nothing up — not that nothing exists. Mathlib moves, so an
entry is only as current as the commits its chapter records.

The statements here are compressed restatements, not quotations, and they carry
the compressor's mistakes. Where one of them and the Lean disagree, the Lean is
right; where one of them and the book disagree, the book is right.


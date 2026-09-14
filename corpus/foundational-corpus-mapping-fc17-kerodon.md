---
type: reference
title: Foundational corpus mapping FC17 Kerodon
description: '# Foundational corpus mapping FC17 Kerodon'
tags:
- project
- reference
timestamp: '2026-09-14T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# FC17 — Kerodon mapping

Canonical catalogue: [[foundational-corpus-units-fc17-kerodon|FC17 — Kerodon]].

Status: **Sweep II open.** The catalogue is complete for the pinned FC17 Kerodon
snapshot, but no unit is cleared for new authorship merely by appearing here.

## Search contract

For every FC17 unit, read the authoritative source statement at its permanent
Kerodon tag before accepting a route. Search pinned/current Mathlib first, then
query the live [Formalization Corpus](https://dzackgarza.github.io/formalization-corpus/)
API as a first-class discovery source, using several mathematically distinct
formulations rather than one literal phrase. The repository client is:

```sh
python scripts/formalization_corpus.py search 'quasicategory inner horn'
python scripts/formalization_corpus.py search 'inner anodyne extension'
python scripts/formalization_corpus.py list 'repo:mathlib4'
```

The service contract is the live OpenAPI document linked by the
[API reference](https://dzackgarza.github.io/formalization-corpus/api.html); that
document, rather than this repository, owns paths, methods, and schemas. Search
results are discovery evidence, not final provenance: open the returned upstream declaration and record its exact
repository/revision/path/name/license/toolchain plus the mathematical comparison
to the full Kerodon obligation.

An `unmatched` route requires the complete negative-search stopping rule in
`AGENTS.md`, including the Formalization Corpus API under multiple source names,
standard synonyms, expected declaration/type fragments, and nearby constructions.
An API outage cannot support `unmatched`.

## Canonical row schema

Append one row per source-unit ID as Mapping proceeds. `Route` is exactly one of
`mathlib`, `project-existing`, `package-import`, `reference-port`, or `unmatched`.
The `Formalization Corpus queries` cell records the dated query batch actually
used; plausible hits are followed to their upstream source before a positive
route is accepted.

| ID | Verdict | Route | Lean target(s) | Provenance | Formalization Corpus queries | Interface comparison |
| --- | --- | --- | --- | --- | --- | --- |

# Data model: the corpus record

The corpus record is Markdown under `corpus/` and two generated files. The tools of D21 in
[research.md](research.md) parse it, so its formats are fixed. This file states the fields that
the tasks cite.

## Source

| Field | Constraint | Owner |
| --- | --- | --- |
| `Source.id` | `FC01`–`FC17`; never renumbered | `corpus/foundational-source-corpus.md` |
| `Source.edition` | the edition, scope and exclusions of the manifest; FC17 is the Kerodon snapshot `corpus/kerodon-source-units.json`, exercises included | manifest |
| `Source.item_key` | the Zotero item key and the key of the extraction attachment (task T002) | manifest |
| `Source.order` | v3 traversal order: FC01, FC02, FC03, FC04, FC05, FC13, FC06, FC07, FC08, FC09, FC10, FC11, FC12, FC14, FC15, FC16, FC17 | manifest |

## Source unit

| Field | Constraint | Owner |
| --- | --- | --- |
| `Unit.id` | `FCxx-<chapter>-Uzzz`, or `FC17-KER-Uzzzzz`; stable through all sweeps | `corpus/foundational-corpus-units-fcxx-*.md` |
| `Unit.kind` | the catalogue kind; the generator classifies the unit as definitional, non-definitional or mixed from the kind and from `[definition-only]` | catalogue, generator |
| `Unit.source_data` | the statement with its hypotheses and data | catalogue |
| `Unit.dependencies` | earlier units needed to state it | catalogue |

A mixed unit contributes its definitional clause to Sweep III and its result clauses to Sweep IV.

## Mapping row

One table row `| \`<unit id>\` | <verdict> | \`<route>\` | <provenance> | ... |` in a chapter,
appendix or source mapping file under `corpus/`.

| Field | Constraint |
| --- | --- |
| `MappingRow.route` | one of `mathlib`, `project-existing`, `package-import`, `reference-port`, `unmatched`; causal provenance, never rewritten after realization |
| `MappingRow.provenance` | repository or package, revision, path, declaration, licence, toolchain and Mathlib compatibility; for `unmatched`, the dated search record |
| `MappingRow.verdict` | the comparison of the source clause with the declarations; carries the markers below |
| `MappingRow.construction_prerequisites` | optional final sentence `Construction prerequisites: \`FCxx-...\`, \`FCxx-...\`.`, full backticked IDs, comma-separated, final period |

### Markers of the verdict

| Marker | Meaning | Set by |
| --- | --- | --- |
| `[negative-search-complete]` | the bounded first-stage search is done; the row is provisional residue | Sweep II |
| `[residue-search-audited]` | the open-ended residue audit is done, with its reproducible record; authorship or local proof is allowed | Sweep II, Sweep IV (D4) |
| `[definition-only]` | the route discharges only the definitional clause of a mixed unit | Sweep II |
| `[realized]` | the Sweep-III realization is accepted; appended, the route and `[residue-search-audited]` stay | Sweep III |
| `[construction-confirmed: Name]` | `Name` is a non-predicate, non-`Prop` declaration in one of the row's Lean files that constructs the row's object | realization-stub audit |
| `[sweep-iii-blocked]` | the recorded route needs a result; the row stays in the population and is re-encoded (D3) | generator rule |

### States of a definitional row

```text
missing -> unmatched -> unmatched [negative-search-complete]
        -> unmatched [negative-search-complete] [residue-search-audited]   (author allowed)
        -> ... [residue-search-audited] [realized]
positive route (mathlib | project-existing | package-import | reference-port)
        -> ... [realized]                                                    (for port or import)
[realized] with a word-net hit -> [construction-confirmed: Name]            (stub audit)
```

A transition that removes `[residue-search-audited]` from an `unmatched` row stops the generator
(`validate_phase_classification`).

## Ledger cell

| Field | Constraint |
| --- | --- |
| `LedgerCell.source` | a `Source.id` |
| `LedgerCell.sweep` | Catalogue, Mapping, Definitions or Theorems |
| `LedgerCell.ticked` | `[x]` only after the whole-source closure check; the ledger `corpus/foundational-corpus-status.md` is the only completion authority |

## Generated selectors

| Selector | Command | Content |
| --- | --- | --- |
| Frontier | `just foundational-frontier` (writes `FOUNDATIONAL_FRONTIER.md`); `python3 scripts/foundational_frontier.py --limit N` to standard output | per unticked cell: delivered and pending counts, next ready units, blockers, mapping actions |
| Definition index | `python3 scripts/foundational_definition_index.py` (writes `FOUNDATIONAL_DEFINITIONS.tsv`) | one row per definitional unit: `unit_id`, `source_id`, `kind`, `label`, `source_location`, `source_data`, `route`, `action`, `search_key`, `mapping_hint`, `mapping_record` |
| Stub population | `python3 scripts/stub_population.py` | one line per `[realized]` row not validly confirmed; empty output is acceptance |
| Output check | `python3 scripts/output_check.py` | the share of the last 20 commits that realized a definition |

## Milestones

| Milestone | Holds when | Performs work |
| --- | --- | --- |
| Milestone 1, `definition-mapping-convergence` | every definitional positive route is verified and every surviving negative row carries `[residue-search-audited]` | no; closed 2026-09-18 |
| Milestone 2, `definition-realization-convergence` | every Definitions cell is ticked and the source-conformance pass found no plausible, partial, weakened or over-specialized row | no |

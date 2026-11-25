# Research: decisions of the foundational corpus programme

Each decision settles a question that `TODO.md`, a sweep record, a vault plan or a governing
document leaves open or answers twice. Each names its source and the text that it supersedes.
The tasks cite decisions by their number.

## D1. One work order

**Decision**: [tasks.md](tasks.md) is the work order of the corpus programme and of the open nodes
of `TODO.md`. It is executed in document order. `TODO.md` keeps the record of the closed nodes and
of the earlier passes, and orders no work. Constitution M11 states this (amendment 1.1.0).

**Source**: constitution M11 and its governance clause; the programme rule that planning happens
only in the Spec Kit workflow.

**Supersedes**: `TODO.md` "Execution DAG" ("the sole executable DAG"), "Active definition units"
("the sole executable unit DAG"), "Where the plans live"; the vault plan
PLAN-FOUNDATIONAL-CORPUS-DEFINITION-SWEEP ("TODO.md remains the sole execution DAG").

## D2. The Sweep-III construction boundary

**Decision**: The proofs that a construction's own data needs are part of the definition: gluing
cocycles and overlap compatibility, quotient descent, well-definedness of the defining map, the
laws that structure fields demand, category and functor laws, independence of representatives.
Results about the finished object (classification, comparison, independence, universal properties
beyond what the construction needs, examples) are Sweep IV. A result is never a prerequisite of a
definition.

**Source**: [corpus-execution.md](../../docs/agents/corpus-execution.md), "Definitions are
constructed, not deferred (2026-09-26)", which states that it wins over older text; the source
manifest, "Sweep-III definition boundary"; `TODO.md`, "Active definition units", "Scope and
acceptance".

**Supersedes**: "There is no proof work in Sweep III" (corpus-execution.md, "Start here", step 4);
LC-03 and LC-20 ("Sweep III contains no proof work"); `TODO.md` lines that say an older trap is
"superseded by the no-proof Sweep-III boundary"; corpus-acceptance.md "Descent, closure,
representative-independence ... are not definition work"; the vault Sweep-III plan, "Mathematical
boundary". Task T003 corrects these texts.

## D3. Rows blocked by the result layer

**Decision**: A pending definition whose frontier blocker is `Sweep-IV result layer` is
re-encoded so that its construction carries its own proofs (D2) and no result is an input. The
marker `[sweep-iii-blocked]` never removes a row from the Definitions population.

**Source**: corpus-execution.md, "Definitions are constructed, not deferred"; the docstring of
`Mapping.sweep_iii_blocked` in `scripts/foundational_frontier.py`.

**Applies to**: `FC06-C02-U156`, `FC06-C03-U107`, `FC06-C03-U175`, `FC11-C09-U005`,
`FC11-C18-U036`, `FC11-C19-U030`, `FC11-C20-U064`, `FC12-C01-U008`, `FC16-C11-U034`.

## D4. Search before a local theorem proof

**Decision**: A theorem unit whose route is `unmatched` without `[residue-search-audited]` gets the
two-stage search (first-stage `[negative-search-complete]`, then the open-ended residue audit and
`[residue-search-audited]`) as the first step of its Sweep-IV task. Only then is it proved locally.
A hit sends the row back to semantic adjudication and the route changes.

**Source**: constitution M8; LC-09; corpus-acceptance.md, "Negative search has two stages"; the
action rule of `scripts/foundational_frontier.py` (`unmatched` gives `residue audit` until the row
is audited, then `author`).

**Supersedes**: the vault Sweep-IV plan, which says only "prove locally only the unmatched
residue".

## D5. Mapping cells

**Decision**: The ticked Mapping cells of FC01–FC15 stand: every unit of those sources has a parsed
mapping row. Their bare `unmatched` theorem rows get the search of D4 inside Sweep IV. FC16 Mapping
closes by the same whole-source rule (every unit has a row; none is missing at `fc549baa`). FC17
Mapping closes when each of its 6,812 units without a row has one.

**Source**: the ledger note in `corpus/foundational-corpus-status.md` (a tick needs a parsed row
for every unit); corpus-acceptance.md, "Close a source from its complete obligations"; the vault
Sweep-II plan, "Handoff to Sweeps III and IV" (Sweep IV resolves the missing non-definitional
mapping before theorem realization).

**Supersedes**: none; the earlier records do not say why FC16 Mapping is unticked.

## D6. Stub rows in a source whose Definitions cell is ticked

**Decision**: The ticks of FC01–FC05 and FC07 stand. A stub-audit row of such a source (FC05: 6,
FC07: 16) that does not construct its object unticks the source's Definitions cell in the commit
that records the finding. The cell is ticked again after the rebuild and the closure check.

**Source**: the ledger note (a tick means the sweep is complete for the whole source);
corpus-acceptance.md (tick only when "no known invalidated mapping or definition remains");
corpus-execution.md, "Not realizations".

## D7. The immediate nodes of `TODO.md`

**Decision**: `padic-realization-acceptance`, `poset-path-lax-functor` and `relative-proj-owner`
are complete as `TODO.md` records. The units listed in `small-reference-ports` are complete: each
mapping row carries `[realized]` and "target-pin acceptance 2026-09-20" (`FC09-C04-U080` and
`FC10-C08-U018` carry `[realized]`). Its continuation is the three pending `reference-port` rows
`FC06-C02-U156`, `FC06-C02-U157`, `FC11-C20-U037`. `lower-ramification-owner` is not Sweep-III
work; its TauCeti route serves the FC09 and FC10 theorem tasks.

**Source**: the mapping rows at `fc549baa`; the `TODO.md` rows themselves.

## D8. The definition-tail buckets

**Decision**: The buckets `tail-fc01`, `tail-fc11`, `tail-fc12`, `tail-misc` held the 2026-09-25
population. The populations now come from [units.md](units.md) and the live selector. The prime
and worker rules stay: the prime alone edits the shared surfaces (`TODO.md` record,
`LeanCategories/All.lean`, `FOUNDATIONAL_DEFINITIONS.tsv`, `FOUNDATIONAL_FRONTIER.md`, the ledger);
workers own disjoint paths and commit by pathspec; acceptance stays with the prime. Before a
dispatch of subagents, the dispatcher states their number, model and token cost, and the
mathematician consents.

**Source**: `TODO.md`, "Subagent buckets for the definition tail"; the owner's standing direction
on the cost of subagent fan-out.

## D9. The orthogonal-group structure theorem

**Decision**: `orthogonal-group-direct-sum-structure` is a consumer request (the research preamble
and the lattice database consume it). It is taken in at once under constitution M9 and does not
wait for Sweep IV. It uses only existing source-faithful definitions; a definition that it needs
and that is missing is realized first, with its source and mapping row.

**Source**: constitution M9, M11; corpus-acceptance.md ("a consumer that genuinely uses an
unproved theorem must depend on that theorem specifically"); the source manifest, "Sweep-IV
theorem boundary"; COMPLAINTS.md, "Orthogonal groups of orthogonal direct sums need their
structure theorem".

**Supersedes**: the `TODO.md` edge `theorems -> orthogonal-group-direct-sum-structure`.

## D10. `computational-core`

**Decision**: The node is executed in `lean-cas-dsl`. The part of this repository is feature
[001](../001-catalogue-inputs-for-the-cas/tasks.md). Feature 002 holds no task for it.

**Source**: the `TODO.md` row; constitution M9, M11.

## D11. Order after Milestone 2

**Decision**: After Milestone 2 the order is: the Sweep-II remainder (FC16 and FC17 Mapping), then
Sweep IV for each source, then `arithmetic-lattice-foundations`, `refactor-audit`, `lint-paydown`,
`bloat-audit-loop`, `abelian-projectivity`.

**Source**: the `Needs` column of the `TODO.md` DAG; the `arithmetic-lattice-foundations` row
("the one-stream queue may still schedule Sweep IV ahead of this row by list order"); the vault
feature FEATURE-FOUNDATIONAL-CORPUS (residual theorem mapping after the definition sweep and
before Sweep IV); constitution M11 (document order).

## D12. Order inside Sweeps III and IV

**Decision**: Sweep IV opens only after Milestone 2 (corpus-wide). Inside a sweep, a unit is ready
when its recorded prerequisites are delivered; the v3 traversal order (FC01, FC02, FC03, FC04,
FC05, FC13, FC06, FC07, FC08, FC09, FC10, FC11, FC12, FC14, FC15, FC16, FC17) breaks ties. A
blocked unit does not hold back an independent ready unit.

**Source**: `TODO.md` (`theorems` needs `definitions`); corpus-execution.md, "Definitions close
before theorems open"; `phase_blocker` in `scripts/foundational_frontier.py`; the source manifest.

## D13. Statement before proof without `sorry`

**Decision**: In Sweep IV the Lean statement of a theorem unit is written in the task record and in
its mapping row, compared with the source and reviewed (constitution M10) before proof work. It
lands in the library only with its proof. No statement-only module with `sorry` exists.

**Source**: `TODO.md` §4a (statements reviewed before proof work caught false statements while
they were cheap); constitution M3 (no `sorry`); constitution M10.

**Supersedes**: the §4a proposal to revisit a statement/proof module split in Sweep IV.

## D14. Module granularity and the axiom roots

**Decision**: Module splits and narrower imports start only from a timing triage table
(constitution E8), when a tier-1 loop of a task of this feature exceeds 300 s (constitution E1).
The root set of the terminal axiom check is settled in source: every constant with prefix
`LeanCategories` or `CasCatalogue` in the environment of `LeanCategories.All`
(`LeanCategories/Tools/AxiomAudit.lean`).

**Source**: constitution E1, E8; `LeanCategories/Tools/AxiomAudit.lean`; feature 001 T001 (the
300 s limit of `just loop`).

**Supersedes**: `TODO.md` §4a ("apply that now"; "settle that root set explicitly").

## D15. Commit, push and CI tiers

**Decision**: The tiers are those of the `justfile`: `test-commit` runs no check, so a partial
unit can be banked; `test-push` runs `lean-no-sorry`; CI runs `just test-ci`, which is `just test`
(build, `lean-no-sorry`, vacuity audit, Mathlib lint audit, unused-variable check, axiom audit).

**Source**: the `justfile` (comment on `test-commit`; recipes `test`, `test-ci`, `test-push`);
constitution M3, E4.

**Supersedes**: `TODO.md` §4a ("`test-push` still delegates to unchanged `test-ci`").

## D16. Access to the sources

**Decision**: A source statement is read through the live Zotero library: the item key and the
page or extraction line (citation-sources.md). The host paths of the manifest are locators on the
owner's workstation. Task T002 records, for each source, its item key and the key of its extraction
attachment in the manifest. A worker that cannot reach the source leaves the unit open.

**Source**: constitution M2; [citation-sources.md](../../docs/agents/citation-sources.md);
LC-19, last sentence; COMPLAINTS.md, "FC03 source manifest points to a missing extracted source
file". At `fc549baa` none of the 16 manifest extraction paths resolves on the container host.

## D17. Source conventions and FOUNDATIONS conventions

**Decision**: A realization states the source's definition. Where the source uses a convention
that FOUNDATIONS.md fixes otherwise (for example Convention 64.9, every ADE lattice negative
definite), the realization carries an explicit comparison to the project convention. A conflict
that changes mathematical content goes to the mathematician (constitution M10).

**Source**: constitution M2, M10; FOUNDATIONS.md §64; AGENTS.md, "Balance autonomous and
interactive work".

## D18. Repairs of the scheduler rows

**Decision**: The three rows that stop the generator are repaired first, in one commit with the
regenerated frontier and definition index. For `FC06-C04-U081` the repair restores the State-1
evidence and `[residue-search-audited]` before `[realized]`; if the history of the row holds no
such evidence, the residue audit is run for it. For `FC15-C06-U009` and `FC15-C06-U012` the
`Construction prerequisites:` clause takes the form that the generator parses.

**Source**: corpus-execution.md, "Repair the scheduler, do not route around it" and "The scheduler
is not the worker's to change" (this feature is the owner's task list); the validator
`validate_phase_classification`.

## D19. Correctness repairs and rework

**Decision**: A false mapping or a wrong definition is repaired when found, with its dependents,
before a dependent unit uses it. Consolidation of correct work (duplicated owners, module layout,
names) waits for `audit-authored-definitions`, `refactor-audit` and `bloat-audit-loop`.

**Source**: corpus-acceptance.md, "Repair the defeated assumption and its affected uses";
`TODO.md` §4a, "Corpus rework is a milestone phase, not continuous".

## D20. The population of the final source-conformance pass

**Decision**: The pass covers every definitional unit of FC01–FC17 (5,054 at `fc549baa`). A row
whose recorded clause comparison names a declaration unchanged since that comparison reuses it;
every other row is compared again.

**Source**: corpus-acceptance.md, "Establish the definition before dependent use" (the
corpus-wide `definition-source-conformance` milestone); corpus-execution.md, "Start here", step 3
("Reuse an established comparison for unchanged declarations").

## D21. Files that stay as tool data

**Decision**: These files are inputs or outputs of the repository's tools. They keep their place
and format.

| File | Tool | Role |
| --- | --- | --- |
| `corpus/foundational-corpus-units-fc*.md` | `foundational_frontier.py`, `foundational_definition_index.py`, `index_kerodon.py` (FC17) | Sweep-I catalogues, input |
| `corpus/*.md` mapping rows (`chapter-*`, `appendix-*`, `foundational-corpus-mapping-*`) | `foundational_frontier.py`, `stub_population.py`, `output_check.py` (`git show -- corpus`) | Sweep-II rows and markers, input |
| `corpus/foundational-corpus-status.md` | `foundational_frontier.py`, `foundational_definition_index.py` | completion ledger, input |
| `corpus/kerodon-source-units.json` | `index_kerodon.py` | FC17 snapshot, input |
| `FOUNDATIONAL_FRONTIER.md` | `just foundational-frontier` | generated output |
| `FOUNDATIONAL_DEFINITIONS.tsv` | `foundational_definition_index.py` (writes), `foundational_definition_candidates.py` (reads) | generated output and input |
| `AGENTS.md`, heading "Definitions are constructed, not deferred" | `output_check.py` (`git log -S` baseline) | the heading text is the baseline of the output check |

`TODO.md` is not tool data: no script, recipe, hook, test or workflow of this repository or of
`ai-review-ci` reads it. No input moves.

**Source**: `git grep` of the file names in `scripts/`, `justfile`, `tests/`, `.github/`,
`site/build.py`, the global hooks and `~/ai-review-ci`.

## D22. The arithmetic and abelian plans

**Decision**: `arithmetic-lattice-foundations` and `abelian-projectivity` keep their requirements
in their vault plans until each becomes a Spec Kit feature of its own. In this feature each is one
task whose acceptance is the plan's success criteria; its first step is that feature's
specification from the vault plan.

**Source**: the `TODO.md` rows; the vault plans PLAN-ARITHMETIC-LATTICE-FOUNDATIONS and
PLAN-ABELIAN-PROJECTIVITY (separate features, 27 and 0 recorded tasks).

# Research: decisions of the foundational corpus programme

Each decision settles a question that `TODO.md`, a sweep record, a vault plan or a governing
document leaves open or answers twice. Each names its source and the text that it supersedes.
The tasks cite decisions by their number.

## D1. One work order

**Decision**: The repository-wide execution order in [tasks.md](tasks.md#repository-wide-execution-order)
selects tasks from their nine owning Spec Kit features under constitution M11 v4.0.0. The task
lists retain the only completion checkboxes; GitHub issues and `TODO.md` retain source and
historical records. Definitions precede independent proof obligations across all features.

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

**Decision**: `padic-realization-acceptance` and `poset-path-lax-functor` are complete as `TODO.md`
records. `relative-proj-owner` is not: its record calls `relativeProjData` the glued scheme, but
that declaration returns the supplied candidate of `RelativeProjPresentationData` (its module
docstring and definition at `a3a66fba`); the glued construction is `CommMon.relativeProj` of #22,
and task T031 realizes `FC06-C02-U231` with it. The units listed in `small-reference-ports` are complete: each
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

**Decision**: M11 v4.0.0 supersedes the former scheduling precedence. Complete the definition
work of the other features before independent Sweep-IV work, and close the Sweep-II remainder
(FC16 and FC17 Mapping) before its theorem units. The continuations retain their full acceptance;
feature 003 and 004 definitions are not held until the corpus theorem sweep closes.

**Source**: the `Needs` column of the `TODO.md` DAG; the `arithmetic-lattice-foundations` row
("the one-stream queue may still schedule Sweep IV ahead of this row by list order"); the vault
feature FEATURE-FOUNDATIONAL-CORPUS (residual theorem mapping after the definition sweep and
before Sweep IV); constitution M11 (definition-first Spec Kit order).

## D12. Order inside Sweeps III and IV

**Decision**: Sweep IV opens only after Milestone 2 (corpus-wide). Inside a sweep, a unit is ready
after the units that it records as prerequisites, which the workstream does first; the v3
traversal order (FC01, FC02, FC03, FC04, FC05, FC13, FC06, FC07, FC08, FC09, FC10, FC11, FC12,
FC14, FC15, FC16, FC17) breaks ties. A unit follows only its own prerequisites.

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
attachment in the manifest. A worker whose host cannot reach the source first makes the admitted
source reachable on that host (the live Zotero library or another copy of the admitted source),
then does the unit (spec, Edge Cases). A source that the library does not hold is added to it
first, by the same rule.

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
names) is done in the tasks of `audit-authored-definitions` (T068), `refactor-audit` (T108) and
`bloat-audit-loop` (T110).

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

**Decision**: `arithmetic-lattice-foundations` is feature
[003](../003-arithmetic-lattice-foundations/spec.md) and `abelian-projectivity` is feature
[004](../004-abelian-projectivity/spec.md). Task T107 executes the tasks of 003 and task T111 executes
004 T001–T010, in the repository-wide M11 bands. These aggregate tasks are acceptance checks,
not execution gates for their definition-bearing child tasks. Feature 003 also
carries the four theorem programmes of the vault feature FEATURE-ARITHMETIC-LATTICE-FOUNDATIONS
(ADE realization, indefinite classification, Siegel mass formula, theta modularity).

**Source**: the `TODO.md` rows; the vault plans PLAN-ARITHMETIC-LATTICE-FOUNDATIONS (27 tasks),
PLAN-ABELIAN-PROJECTIVITY (0 tasks) and their four sibling plans, now archived as superseded by
features 003 and 004; 003 research D1, D2; 004 research D2.

## D23. Open requests and defects recorded in COMPLAINTS.md

**Decision**: Every open formalization request that COMPLAINTS.md records for this repository has a
task. A consumer request (a research, Coble, Looijenga, AET, Satake or catalogue consumer) is a
Phase 2 task (T112–T125), taken in at once (constitution M9). A lattice or form item that belongs to
the arithmetic foundation is a task of feature 003 (003 research D25). A gate, contribution-rule or
tooling defect is a Phase 1 task (T126–T129). A request of the registry and catalogue surface is
feature 001's. Each task first compares its entry with the source at its revision, because an entry
can lag a repair (for example the gallery bridge of #181 is now proved in
`ForMathlib/RootSystem/WythoffAscent.lean`).

**Source**: constitution M9, M12; LC-05 ("On resolution, verify the full unmet requirement");
LC-11; COMPLAINTS.md, read in full at `533e9259`; the closed GitHub issues #26, #27, #37, #88,
#91, #141, #162, #167, #171, whose residual items live only in COMPLAINTS.md.

## D24. Gate, environment and consumer issues outside COMPLAINTS.md

**Decision**: #144 (the gate builds only the import closure of the root module) and #118 (build
and test inside the research image on its shared Mathlib) are gate and environment defects and are
Phase 1 tasks (T130, T131); T130 precedes T129 so that the green gate covers every module. #89 (the
presentations of $\mathrm{SL}_2(\mathbb Z)$ and $\mathrm{GL}_2(\mathbb Z)$ for the research preamble)
and #178 (Tor one for arbitrary $A$ for a qualifying-exam card) are consumer requests and are Phase 2
tasks (T132, T133), taken in at once (constitution M9). The repository pin follows the research
image's Mathlib at `master`; a Mathlib change that breaks the build is repaired in source.

**Source**: #144 and its comment of 2026-11-15; #118, body and the owner decisions of 2026-11-10 and
2026-11-11 recorded there; #89; #178; constitution M3, M9, E5.

## D25. Research-book foundation intake (#226)

**Source:** [Pinned catalogue, 2026-11-27](https://gist.githubusercontent.com/dzackgarza/7486d053f8ee3fe3165c0d64bcbf1fc8/raw/df4cdf1b6ee1b6bb0f438e7982265cf7aa2e8e1f/lean-formalization-catalogue.md),
SHA-256 `861b3de5a849c8726f706edda2c4a0985e720e33b128b163462a5a4a9a6353e9`, and
[#226](https://github.com/dzackgarza/lean-categories/issues/226). The fetched snapshot was
hash-verified on 2026-11-27; it contains 2,053 catalogue entry headings (including 512
Definition, 29 Construction, 29 Notation, and mixed content in other entry kinds). These are
source-entry counts, not counts of missing declarations. The admitted FC01–FC17 sources are
unchanged.

**Decision:** Apply M2, M4, M8–M11 and LC-02/09/17/19 to all labels, including statement and proof
citations separately. T134 owns source intake and the definition layer; T135 owns the proof
layer. Route each uncovered obligation to an existing feature before creating any new feature.
No new axiom, unproved conjecture or false definition is inferred from the book's unresolved
uses. Only the actual reviewed declarations and original acceptance discharge #226.

# Implementation Plan: The foundational corpus programme

**Branch**: `002-foundational-corpus-sweeps` (work lands on `main`) | **Date**: 2026-11-25 | **Spec**: [spec.md](spec.md)
**Input**: Feature specification from `specs/002-foundational-corpus-sweeps/spec.md`

Revision of record: `fc549baa`. The decisions D1–D23 are in [research.md](research.md); the
record formats in [data-model.md](data-model.md); the unit populations in [units.md](units.md);
the validation runs in [quickstart.md](quickstart.md).

## Summary

The programme realizes the seventeen corpus sources in four sweeps. Sweep I is complete. The
remaining work, in task order: repair the three mapping rows that stop the frontier generator;
take in the consumer requests (M9): the orthogonal-group structure theorem and the open
requests of COMPLAINTS.md; finish Sweep III
(the stub audit of 125 rows, the 35 pending definitions, the closure of 11 Definitions cells, the
ownership audit and the source-conformance pass over 5,054 definitional units, Milestone 2);
finish Sweep II (FC16, FC17); run Sweep IV over 12,952 pending theorem units in 17 catalogue
tasks; then the continuations of the `TODO.md` DAG, of which the arithmetic lattice theory and
abelian projectivity are features 003 and 004.

## Technical Context

**Language/Version**: Lean 4, toolchain of `lean-toolchain` (`leanprover/lean4:v4.36.0`)
**Primary Dependencies**: Mathlib (`rev = "master"`, locked in `lake-manifest.json`), BrauerGroup (`bb53b6f9`)
**Storage**: Lean source under `LeanCategories/`; the corpus record under `corpus/` (Markdown, parsed by the tools of D21)
**Testing**: tier-1 elaboration of each changed module; the selector commands of [data-model.md](data-model.md); `just test` at milestones; CI `just test-ci`
**Target Platform**: Linux, research image `ghcr.io/dzackgarza/sage:develop` (constitution E5)
**Project Type**: Lean library (formal mathematics and its source record)
**Performance Goals**: tier-1 loop of each change under 300 s (constitution E1, E4)
**Constraints**: one Lean process under `flock .tmp/lean.lock` (E10); no `sorry`, no project axiom (M3); source statements read from the live library (D16)
**Scale/Scope**: 17 sources; 19,004 catalogue units at `fc549baa`: 5,054 definitional and 15,363 non-definitional, of which 1,413 mixed units count in both

## Constitution Check

| Article | Check for this feature | Status |
| --- | --- | --- |
| M1 | Every definition and theorem is mathematics of this repository, from its source | pass: inputs are the catalogues, the sources and this repository |
| M2 | Each acceptance compares the declaration with the source clause read on the page | Contracts D, R, T; D16, D17 |
| M3 | No `sorry`, no project axiom; `just test` at milestones | Contracts C, D and T; T086 |
| M4 | Each definition at its generating category; inheritance by structural functors | Contract D |
| M5 | Total operations on their domains; numerals as universal images | Contract D (LC-14, LC-15, LC-18) |
| M6 | Typed identity; comparison cells; chosen structure as data | Contract D |
| M7 | Registry rows name the corpus declaration | FR-024; Contract D |
| M8 | Search record before authoring, in the mapping row | Search before authoring; D4 |
| M9 | Consumer requests taken in at once | T004–T008 (D9), T112–T125 (D23) |
| M10 | Independent review; content changes go to the mathematician | Contract R; D17 |
| M11 | This task list in document order; `TODO.md` orders nothing | D1; constitution 2.0.0 |
| M12 | Issues in COMPLAINTS.md; workarounds with the five fields of LC-12 | FR-020; every contract |
| M13 | No artifact certifies itself; a worker's report is evidence only | Contract R |
| E1, E4 | Tier 1 per change, under 300 s; long runs at milestones | Checks of this repository |
| E2 | Tests through the public declarations; no stand-in rows | Contracts D, T |
| E5 | One platform: Linux and the research image | Technical Context |
| E3 | Policy corrections show a defective contribution beside its replacement | T003 |
| E6, E7 | Durable logs and timing records | feature 001 T002, T003; `scripts/build-timing.sh` |
| E8 | Optimization only from a timing triage table | D14 |
| E9 | Construction close to instant; expensive work deferred | Contract D |
| E10 | One Lean process; forward history; state inside the repository | Checks of this repository |

Gate result: pass. No violation is justified in Complexity Tracking.

## Checks of this repository

| Tier | Command | Source |
| --- | --- | --- |
| Tier 1 | `flock .tmp/lean.lock lake env lean <module>` for each changed module and each module that imports it in the change; after feature 001 T001, `just loop <modules>` | constitution E1; `TODO.md`, "One Lean process" |
| Selector | `just foundational-frontier`; `python3 scripts/foundational_definition_index.py`; `python3 scripts/stub_population.py`; `python3 scripts/output_check.py` before each new unit | [data-model.md](data-model.md) |
| Commit | `just test-commit` (no check; a partial unit can be banked) | `justfile`; D15 |
| Push | `test-push` (`lean-no-sorry`) | `justfile`; D15 |
| Full gate | `just test` (build, `lean-no-sorry`, vacuity audit, Mathlib lint audit, unused-variable check, axiom audit) | `justfile`; constitution M3 |
| CI | `just test-ci` on push | `.github/workflows/ci.yml` |

Before any Lean process: `pgrep -a -x 'lean|lake'` prints nothing, and `free -m` shows room for one
process (AGENTS.md, "One Lean process at a time"). A wait on a long process checks that the
process is alive (LC-08).

## The sweeps and their order

| Phase of tasks.md | Sweep | Gate to enter | Gate to leave |
| --- | --- | --- | --- |
| 1 | records and gates | none | the generator exits 0; `just test` green (T129) |
| 2 | M9 intake | none | each request's statements proved at their owners |
| 3, 4 | III | Milestone 1 (closed 2026-09-18) | every Definitions cell ticked |
| 5 | III | every Definitions cell ticked | ownership audit converged |
| 6 | III | ownership audit converged | Milestone 2 |
| 7 | II | Milestone 2 (scheduling precedence, D11) | FC16, FC17 Mapping ticked |
| 8 | IV | Milestone 2 and, per source, its Mapping cell | every Theorems cell ticked |
| 9 | continuations | the `Needs` of the `TODO.md` DAG (D11) | each node's acceptance; T107 is feature 003 and T111 feature 004 (D22) |

Inside a phase, a unit is ready when its recorded prerequisites are delivered; source order breaks
ties (D12). A blocked unit does not hold back an independent ready unit.

## Source catalogues

| Source | Catalogue | Source mapping record | Owner directories of its realizations |
| --- | --- | --- | --- |
| FC01 Dummit–Foote | `corpus/foundational-corpus-units-fc01-dummit-foote.md` | `corpus/foundational-corpus-mapping-fc01-dummit-foote.md` | `Algebra/`, `Modules/`, `LinearAlgebra/` |
| FC02 Munkres | `...-fc02-munkres.md` | `...-mapping-fc02-munkres.md` | `Topology/` |
| FC03 Riehl | `...-fc03-riehl-category-theory-in-context.md` | `...-mapping-fc03-riehl-category-theory-in-context.md` | `CategoryTheory/`, `ForMathlib/` |
| FC04 Atiyah–Macdonald | `...-fc04-atiyah-macdonald.md` | `...-mapping-fc04-atiyah-macdonald.md` | `RingTheory/`, `Modules/` |
| FC05 Weibel | `...-fc05-weibel.md` | `...-mapping-fc05-weibel.md` | `Homological/` |
| FC13 Matsumura | `...-fc13-matsumura.md` | `...-mapping-fc13-matsumura.md` | `RingTheory/` |
| FC06 Hartshorne | `...-fc06-hartshorne.md` | `...-mapping-fc06-hartshorne.md` | `Schemes/`, `AlgebraicGeometry/`, `Homological/` |
| FC07 Hatcher | `...-fc07-hatcher.md` | `...-mapping-fc07-hatcher.md` | `Topology/`, `Homological/` |
| FC08 Lee | `...-fc08-lee.md` | `...-mapping-fc08-lee.md` | `Geometry/`, `Analysis/` |
| FC09 Neukirch | `...-fc09-neukirch.md` | `...-mapping-fc09-neukirch.md` | `Algebra/`, `RingTheory/` |
| FC10 Serre | `...-fc10-serre-local-fields.md` | `...-mapping-fc10-serre-local-fields.md` | `Algebra/`, `RingTheory/`, `Homological/` |
| FC11 Peters–Sterk | `...-fc11-peters-sterk.md` | `...-mapping-fc11-peters-sterk.md` | `Lattices/`, `Modules/Bilinear/`, `Modules/Quadratic/`, `Geometry/` |
| FC12 Beauville | `...-fc12-beauville.md` | `...-mapping-fc12-beauville.md` | `Schemes/`, `AlgebraicGeometry/`, `Geometry/` |
| FC14 Humphreys, Lie algebras | `...-fc14-humphreys.md` | `...-mapping-fc14-humphreys.md` | `Algebra/` (Lie theory), `Exceptional/` |
| FC15 Humphreys, Coxeter groups | `...-fc15-humphreys-reflection-groups-and-coxeter-groups.md` | `...-mapping-fc15-humphreys-reflection-groups-and-coxeter-groups.md` | `Algebra/`, `Combinatorics/` |
| FC16 Humphreys, algebraic groups | `...-fc16-humphreys-linear-algebraic-groups.md` | `...-mapping-fc16-humphreys-linear-algebraic-groups.md` | `AlgebraicGeometry/`, `Schemes/` |
| FC17 Kerodon | `...-fc17-kerodon.md` (from `corpus/kerodon-source-units.json`) | `...-mapping-fc17-kerodon.md` | `CategoryTheory/`, `ForMathlib/` |

The per-unit rows of a source are in its chapter and appendix files under `corpus/`, which the
source mapping record links. The owner directory of a new declaration follows M4: the lowest
mathematical owner, not the source. The directories above are the owners of the existing
realizations of each source, as named in the mapping rows.

## Search before authoring

Every definition, every theorem and every lemma inside a proof is searched before it is written
(constitution M8, LC-09). The record is written in the unit's mapping row; the commit cites it.

1. Read the candidate census of the definition index (`search_key`, `mapping_hint`) and the row.
2. Search pinned Mathlib (`.lake/packages/mathlib/Mathlib`), current upstream Mathlib and its open
   pull requests, under the source name, its synonyms, the dual notion, the expected declaration
   name and type shape.
3. Search the live Formalization Corpus API:
   `python scripts/formalization_corpus.py search '<query>'` under each formulation;
   `python scripts/formalization_corpus.py batch` for a batch; refine with `repo:` and `file:` only
   after the broad query.
4. Search Loogle, LeanSearch, the Mathlib documentation, Reservoir, GitHub code search across Lean
   repositories, the proof-assistant repositories that the corpus indexes, `formal-conjectures`,
   the locally mirrored reference corpora, and the formalization source atlas
   (`corpus/lean-formalization-source-atlas-and-research-log.md`).
5. Open each plausible candidate at its revision and compare its inputs, outputs, hypotheses and
   generality with the source clause (corpus-acceptance.md, "Accept a mapping against the whole
   source obligation").
6. Record the date, the object sought, the queries, the surfaces, the revisions, the candidates
   and the reason each fails. Set `[negative-search-complete]` after the bounded pass and
   `[residue-search-audited]` after the open-ended pass. A surface that the worker cannot reach is
   not counted as searched.
7. A substantial support layer of a construction gets its own search (FR-011).

## Unit contracts

The tasks name these contracts instead of repeating them.

**Contract S (stub audit row).** Open the declaration that the row names. If a `def`, `abbrev`,
`structure`, `class`, `inductive` or `instance` that is not a predicate constructs the row's
object from the source's inputs, append `[construction-confirmed: Namespace.decl]`. If the object
is a parameter, a hypothesis, a candidate, an `Is…Data` predicate or the graph of a supplied map,
build the object under Contract D and confirm it in the commit that lands the construction. A
rebuild of a row of a ticked source follows D6. Check: the row is absent from
`python3 scripts/stub_population.py`; tier 1 on each changed module.

**Contract D (definition unit).** Read the source clause from the library (D16) and the row, and
write the source record of mathematical-simplicity.md, "Source the definition before proving its
theorems", in the row. Split
the definitional clause from the result clauses. For `reference-port`, port the recorded reference
with its provenance; for `package-import`, import the package; for `unmatched`
`[residue-search-audited]`, author. Place the declaration at its generating category (M4); obtain
richer cases by structural functors; take each object in the category that carries its structure
(LC-13); keep every operation total on its domain (LC-14). Include the proofs that the
construction's own data needs (D2); make no result a prerequisite (D3). Search each substantial
support layer first (FR-011). State the source's convention and compare it with a FOUNDATIONS
convention where they differ (D17). Run the wrong-model test and one positive and one separating
example from the source (mathematical-simplicity.md). Add new modules to `LeanCategories/All.lean`.
Append `[realized]` to the verdict, keep the route and `[residue-search-audited]`, and record the
clause comparison. A registry row of `LeanCategories/Catalogue/` for the same object names this
declaration (M7); a second declaration of the same object is a duplicate owner (D19). Regenerate
the definition index and the frontier in the same commit. Check:
tier 1; `just foundational-frontier` exits 0; the unit leaves the pending population; the axiom
audit admits only standard axioms at the next full gate. Review: Contract R.

**Contract C (closure of a cell).** Return to the complete unit population of the source for the
sweep. For each unit with content of the sweep, name the evidence that discharges it (the
realizing declaration, or for Mapping the route and comparison or the scoped search). Check that
no known invalid mapping or definition remains in the source. Tick the cell in
`corpus/foundational-corpus-status.md` in the commit that carries the last unit of the source;
regenerate the frontier in that commit.

**Contract R (review).** A reviewer who did not write the change compares the source clause with
the declaration: data, constructors, fields, hypotheses, quantified parameters, variance,
universes and generality, quotient or representative data, notation. The reviewer reads the
meaning of each project-owned premise and applies the unfolding and theorem-survival tests of
mathematical-simplicity.md. A mismatch removes `[realized]`, is recorded under LC-05,
and reopens the owner and every dependent realization (corpus-acceptance.md, "Repair the defeated
assumption"). A change of mathematical content goes to the mathematician (M10).

**Contract M (mapping row).** Read the unit's source statement and write one row in the chapter
file of the unit: route class, provenance, comparison of the whole source obligation with the
candidate declarations, or the scoped dated search. Check: the row parses (the generator exits 0)
and the unit leaves the missing population.

**Contract T (theorem unit).** If the route is `unmatched` without `[residue-search-audited]`, run
the search (D4) first. Write the Lean statement with the source's exact hypotheses and conclusion
over the corpus definitions; record it in the row; have it reviewed (Contract R, statement only)
before proof work (D13). Reuse a `mathlib`, `project-existing` or `package-import` proof; port a
`reference-port` proof with provenance; else prove. Never change a completed definition to make a
proof easier; never add an axiom, a theorem-shaped field or a stronger definition. Append
`[realized]` to the row. Check: tier 1; the unit leaves the pending population; the axiom audit at
the next full gate.

## How the frontier is regenerated

`just foundational-frontier` runs `python3 scripts/foundational_frontier.py > FOUNDATIONAL_FRONTIER.md`.
The generator parses the ledger, every mapping row under `corpus/` and every catalogue, validates
the phase classification, and writes for each unticked ledger cell its delivered and pending
counts and its next five ready units (`--limit N` shows more on standard output). It never ticks a
cell. `python3 scripts/foundational_definition_index.py` writes `FOUNDATIONAL_DEFINITIONS.tsv`.
Both regenerate in the commit that changes the mapping state (FR-018). At `fc549baa` the generator
fails on three rows (units.md, "Scheduler defects"); task T001 repairs them. A failure of the
generator stops unit selection until it is repaired (corpus-execution.md, "Repair the scheduler").

## Files that stay as tool data

The table of [D21](research.md#d21-files-that-stay-as-tool-data) lists the inputs and outputs of
the tools. They keep their place and format. `TODO.md` is not tool data; it is the record of the
closed DAG nodes and of the earlier sweep passes, and it points to this task list as the work
order. No tool input moves, so no task moves one.

## Project Structure

### Documentation (this feature)

```text
specs/002-foundational-corpus-sweeps/
├── spec.md              # requirements, user stories, success criteria
├── plan.md              # this file
├── research.md          # decisions D1–D23 with their sources
├── data-model.md        # formats of the corpus record
├── quickstart.md        # validation runs
├── units.md             # unit populations at fc549baa
├── checklists/
│   └── requirements.md  # spec quality checklist
└── tasks.md             # the work order
```

### Source Code (repository root)

```text
corpus/                  # catalogues, mapping rows, manifest, ledger (tool data, D21)
LeanCategories/          # realizations at their mathematical owners; All.lean imports every module
scripts/                 # frontier, definition index, candidates, stub population, output check
tests/                   # scheduler regression tests (owner surface, FR-019)
FOUNDATIONAL_FRONTIER.md
FOUNDATIONAL_DEFINITIONS.tsv
```

**Structure Decision**: no new directory. Every realization goes to the owner that M4 selects;
every record change goes to the existing row of its unit.

## Complexity Tracking

No constitution violation needs justification.

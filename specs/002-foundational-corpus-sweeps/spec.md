# Feature Specification: The foundational corpus programme

**Feature Branch**: `002-foundational-corpus-sweeps` (work lands on `main`)

**Created**: 2026-11-25

**Status**: Planned

**Input**: The formalization corpus programme of this repository, planned only in Spec Kit, with
every decision of its earlier records settled here.

The corpus is the fixed list of seventeen textbook sources `FC01`–`FC17` of the
[source manifest](../../corpus/foundational-source-corpus.md) (corpus v1 with the v2 and v3
amendments). The programme delivers, for every formal unit of these sources, its Lean realization
in this repository: each definition is the object that the source defines, built from the
source's inputs, at the category that generates it; each theorem is proved with the source's
hypotheses and conclusion. The library has no `sorry` and no project axiom (constitution M3).

Four sweeps traverse the same source-unit IDs:

| Sweep | What it establishes | State |
| --- | --- | --- |
| I. Catalogue | Every formal unit of each source has a stable ID, a location, a kind, its data and hypotheses, and its source dependencies, independently of Lean | complete for FC01–FC17 |
| II. Mapping | Every unit has one route record: an existing owner (`mathlib`, `project-existing`, `package-import`, `reference-port`) with provenance, or `unmatched` with a reproducible search record | open for FC16 and FC17 |
| III. Definitions | Every definitional unit has a realization that constructs the source object, and a final audit confirms it against the source (Milestone 2) | open for FC06, FC08–FC17 |
| IV. Theorems | Every non-definitional unit is reused, ported or proved with its exact hypotheses | open for FC01–FC17 |

The counts are in [Success Criteria](#success-criteria-mandatory) and, per unit, in
[units.md](units.md).

## User Scenarios & Testing *(mandatory)*

### User Story 1 - A mathematician looks up a definition with its source (Priority: P1)

A mathematician has a source unit, for example Hartshorne II.7 relative $\operatorname{Proj}$ and
$\mathcal O(1)$ (`FC06-C02-U231`). The mathematician finds the Lean declaration that constructs
that object, the category that owns it, the route that supplied it, and the source locator
(library item key and page). The declaration takes the source's inputs and returns the source's
object. It does not take the object as a parameter, a hypothesis or a candidate.

**Why this priority**: The corpus is worth something only when each object in it is the object
that the literature names. This is the first use of the corpus and the input of every later
sweep.

**Independent Test**: Take a realized unit from the definition index. Follow its mapping row to
the declaration. Read the declaration's type and the source clause. The type is the source object
built from the source inputs, the module is imported by `LeanCategories/All.lean`, and the axiom
audit admits only the standard axioms.

**Acceptance Scenarios**:

1. **Given** a definitional unit whose mapping verdict carries `[realized]`, **When** the
   mathematician reads its row, **Then** the row names one constructing declaration in a named
   Lean file, the route, the provenance and the source comparison.
2. **Given** a unit whose route is `mathlib` or `project-existing`, **When** the mathematician
   follows the row, **Then** the row names the existing owner and the specialization that makes
   the source notion an instance of it; no second declaration exists for the same object.
3. **Given** a source definition stated with a convention that differs from a convention of
   [FOUNDATIONS.md](../../FOUNDATIONS.md) (for example a sign convention for $E_8$), **When** the
   mathematician reads the realization, **Then** it states the source's definition and an explicit
   comparison to the project convention.

---

### User Story 2 - A consumer reads the registry (Priority: P1)

A consumer (the kernel of `lean-cas-dsl`, a research notebook, the published corpus site) reads
the corpus record at a pinned revision. For every unit it obtains the route, the realizing
declaration and the state of each sweep. The record regenerates from the catalogues, the mapping
records and the ledger without error. A row of the semantic registry (`LeanCategories/Catalogue/`)
whose object is a corpus object names the same declaration as the corpus record.

**Why this priority**: The scheduler and the registry are the instruments that decide what is
built next and what downstream may use. A record that does not regenerate returns unit selection
to whoever reads it.

**Independent Test**: At a pinned revision, regenerate the frontier (`just foundational-frontier`)
and the definition index (`python3 scripts/foundational_definition_index.py`). Both exit 0. Every
catalogue unit has exactly one mapping row. For each registry row that cites a corpus unit, the row's
declaration equals the declaration of the unit's mapping row.

**Acceptance Scenarios**:

1. **Given** the current `main`, **When** the frontier generator runs, **Then** it exits 0 and
   names the next ready units of every unticked ledger cell that has pending units.
2. **Given** a unit ID, **When** a consumer reads the definition index, **Then** it obtains the
   source data, the route and the action of that unit.
3. **Given** a ledger cell, **When** a consumer reads it, **Then** a tick means that the sweep is
   complete for the whole source, and no other file claims sweep completion.

---

### User Story 3 - A reviewer checks a definition against its source (Priority: P1)

A reviewer who did not write the definition opens the source clause, the mapping row and the
declaration. The reviewer compares the definitional data, the hypotheses, the quantified
parameters, the variance, the generality and the quotient or representative data, clause by
clause. The reviewer also checks one positive and one separating example from the source. A
mismatch reopens the owning definition and every realization that depends on it.

**Why this priority**: Compilation, familiar names and downstream theorems are not evidence of
fidelity (constitution M2). Only an independent source comparison is.

**Independent Test**: Take a realized definitional unit. Without the author's report, compare the
source clause and the declaration. The comparison recorded in the mapping row agrees with the
reviewer's comparison, or the reviewer records the mismatch under LC-05 and the row loses
`[realized]` until the owner is repaired.

**Acceptance Scenarios**:

1. **Given** a definition whose encoding needs a gluing, descent or well-definedness proof for its
   own data, **When** the reviewer reads it, **Then** that proof is present in the construction,
   and no result about the finished object is a prerequisite of it.
2. **Given** the final source-conformance pass, **When** it ends, **Then** every one of the
   definitional units of FC01–FC17 has a usable realization that agrees with its source, and
   Milestone 2 holds.

---

### User Story 4 - A mathematician uses a source theorem at its owner (Priority: P2)

A mathematician cites a lemma, proposition, theorem, corollary or admitted example of a corpus
source. The mathematician finds the Lean theorem with the source's exact hypotheses and
conclusion, stated about the corpus definitions, proved without `sorry` or a project axiom, or
the reused or ported proof with its provenance.

**Why this priority**: The theorem layer depends on the complete definition layer and is the long
part of the programme. It must not weaken or delay the definitions.

**Independent Test**: Take a theorem unit whose Theorems cell is ticked. Its mapping row names the
proof; the statement agrees with the source clause; the axiom audit admits only standard axioms.

**Acceptance Scenarios**:

1. **Given** an `unmatched` theorem row, **When** its work starts, **Then** the search record of
   constitution M8 exists in the row and carries `[residue-search-audited]` before any local proof.
2. **Given** a hard theorem, **When** it stays open, **Then** no axiom, theorem-shaped structure
   field, stronger definition or weaker statement stands in for it.

---

### User Story 5 - A research consumer builds on the corpus vocabulary (Priority: P3)

A research workstream needs mathematics on top of the corpus: the structure theorem for
orthogonal groups of orthogonal direct sums of definite lattices, the arithmetic lattice theory
at its natural generality, or the projective realization of polarized complex tori. It obtains
that mathematics here, stated on the corpus definitions, without a local substitute.

**Why this priority**: These programmes consume the corpus. One of them is a consumer request
that constitution M9 takes in at once.

**Independent Test**: Each continuation's success criteria hold at their owners, and no corpus
definition is duplicated.

**Acceptance Scenarios**:

1. **Given** a consumer request for a theorem, **When** it arrives, **Then** it is taken in at
   once and depends only on the exact units that it uses, not on the whole theorem sweep.

---

### Edge Cases

- A source unit mixes a definition and a result. Its definitional clause belongs to Sweep III and
  its result clauses to Sweep IV; the unit keeps one ID.
- A mapping route records a dependency on a result (`Sweep-IV result layer` in the frontier). The
  definition is re-encoded so that no result is its prerequisite.
- A definition is out of reach. What is missing is more definitions, or a source that states the
  construction; those become prerequisite units.
- A realization needs a substantial support layer that the parent search did not cover. The
  support is searched on its own before it is written.
- A row of a source whose Definitions cell is ticked fails the stub audit. The cell is unticked
  until the row is rebuilt and the source closes again.
- The source text is not reachable on the worker's host. The unit stays open; lack of access is
  not a negative search result.
- The generator fails on a malformed or inconsistent mapping row. The row is repaired before more
  units are selected.
- A consumer needs a theorem before Sweep IV opens. The theorem is taken in under M9 and uses only
  existing source-faithful definitions; a definition that it needs and that is missing is
  realized first as a definition unit.
- FC17 admits its exercises (manifest, v3 amendment); FC01–FC16 exclude exercises. An FC17
  exercise is a non-definitional unit.

## Requirements *(mandatory)*

### Functional Requirements

**Scope and sources**

- **FR-001**: The corpus MUST be exactly the sources, editions and scopes of the source manifest.
  A change of membership, order, edition or scope MUST be a new corpus-version amendment.
- **FR-002**: Every acceptance decision that compares a declaration with its source MUST rest on
  the source statement read from the admitted source, located by its library item key and page
  ([citation-sources.md](../../docs/agents/citation-sources.md), constitution M2).
- **FR-003**: The Sweep-I catalogues MUST stay the only authority for unit IDs, kinds and source
  data. A catalogue defect MUST be repaired in the catalogue, recorded under LC-05, and every
  closure claim that used the defective selection MUST be checked again.

**Mapping (Sweep II)**

- **FR-004**: Every catalogue unit MUST have exactly one mapping row with one route class and its
  provenance (repository, revision, path, declaration, licence, toolchain) or a dated, scoped
  negative search.
- **FR-005**: No definition MUST be authored and no theorem MUST be proved locally before its row
  holds the reproducible two-stage search record and `[residue-search-audited]` (constitution M8,
  LC-09, LC-19).
- **FR-006**: A route MUST stay the causal provenance of the work. Realization MUST append
  `[realized]` to the verdict and MUST keep `[residue-search-audited]` and the route.

**Definitions (Sweep III)**

- **FR-007**: Every definitional unit MUST have a declaration that constructs the source's object
  from the source's inputs, at the lowest category that generates it, obtained elsewhere by
  composition with structural functors (constitution M4).
- **FR-008**: The proofs that a construction's own data needs (gluing and overlap compatibility,
  quotient descent, well-definedness of the defining map, the laws that structure fields demand,
  category and functor laws) MUST be part of the construction. A result about the finished object
  MUST NOT be a prerequisite of a definition.
- **FR-009**: A declaration that takes its object as a parameter, an instance argument or a
  hypothesis, a candidate or specification-only value, or a row removed from the population or
  marked blocked MUST NOT count as a realization.
- **FR-010**: Every `[realized]` row that the stub audit selects MUST name its constructing
  declaration with `[construction-confirmed: Name]`, or MUST be rebuilt as a construction.
- **FR-011**: A substantial support layer (a new reusable structure, predicate, quotient framework
  or replacement theory) MUST be searched on its own, and MUST be reused, imported or ported
  before it is authored.
- **FR-012**: A realization MUST state the source's definition. Where a source convention differs
  from a FOUNDATIONS convention, the realization MUST carry an explicit comparison and MUST NOT
  switch convention silently.
- **FR-013**: A source's Definitions cell MUST be ticked only after the whole-source closure check
  of [corpus-acceptance.md](../../docs/agents/corpus-acceptance.md#close-a-source-from-its-complete-obligations).
  The ledger MUST stay the only completion authority.
- **FR-014**: After every Definitions cell closes, an ownership audit MUST replace every project
  owner that duplicates a checked external owner, unless the source interface requires it.
- **FR-015**: A final source-conformance pass MUST compare every definitional unit with its
  source and its realization. Milestone 2 MUST hold only when no row is plausible, partial,
  weakened or over-specialized.

**Theorems (Sweep IV)**

- **FR-016**: Every non-definitional unit MUST be reused, ported or proved with its exact
  hypotheses and conclusion, after Milestone 2. No axiom, theorem-shaped field, stronger
  definition or weaker statement MUST stand in for an open theorem.
- **FR-017**: Before proof work, the statement of a theorem unit MUST be compared with the source
  and reviewed. No statement MUST land with `sorry`.

**Records and tools**

- **FR-018**: The frontier generator and the definition index MUST regenerate without error at
  every commit on `main`, and MUST be regenerated in the commit that changes the mapping state.
- **FR-019**: The scheduler (`scripts/foundational_frontier.py`,
  `scripts/foundational_definition_index.py`, their tests and the population markers) MUST change
  only through a task of this feature.
- **FR-020**: Every mathematical issue, missing theorem and workaround MUST be recorded in
  [COMPLAINTS.md](../../COMPLAINTS.md) under LC-05, LC-11 and LC-12.

**Checks**

- **FR-021**: Each change MUST pass tier 1 (constitution E1); each milestone MUST pass `just test`;
  the library MUST hold no `sorry` and no project axiom (constitution M3).
- **FR-022**: Only one Lean process MUST run on the host, under `flock .tmp/lean.lock`
  (constitution E10).

**Consumers and work order**

- **FR-023**: A consumer's request for missing mathematics MUST be taken in at once and MUST
  depend only on the exact units that it uses (constitution M9).
- **FR-024**: A semantic registry row whose object is a corpus object MUST name the declaration of
  that unit's mapping row (constitution M7).
- **FR-025**: [tasks.md](tasks.md) MUST be the work order of the programme, executed in document
  order (constitution M11). `TODO.md` MUST NOT order work.
- **FR-026**: Every open formalization request, gate defect, contribution-rule defect and tooling
  defect that
  [COMPLAINTS.md](../../COMPLAINTS.md) records for this repository MUST have a task: a consumer
  request in Phase 2 of this feature, a gate, rule or tooling defect in Phase 1, a foundation item
  of the arithmetic lattice theory in feature 003, a registry or catalogue item in feature 001
  (research D23).

### Key Entities

- **Source**: one admitted textbook or snapshot `FCxx`, with its edition, scope and library item.
- **Source unit**: one formal unit `FCxx-Cyy-Uzzz` (FC17: `FC17-KER-Uzzzzz`) with kind, source data
  and source dependencies.
- **Mapping row**: the route record of one unit, with its markers (`[negative-search-complete]`,
  `[residue-search-audited]`, `[definition-only]`, `[realized]`, `[construction-confirmed: Name]`).
- **Ledger cell**: the whole-source completion state of one source and one sweep.
- **Frontier and definition index**: the generated selectors of ready units.
- **Milestone**: a state transition that certifies a sweep's convergence and performs no work.

Their fields and states are in [data-model.md](data-model.md).

## Success Criteria *(mandatory)*

### Measurable Outcomes

The start values are the selector at `fc549baa` ([units.md](units.md)).

| Outcome | Start | Target |
| --- | --- | --- |
| Generator defects that stop the frontier | 3 | 0 |
| Unticked ledger cells | 30 | 0 |
| Unticked Mapping cells (FC16, FC17) | 2 | 0 |
| Catalogue units without a mapping row (FC17) | 6,812 | 0 |
| Unticked Definitions cells | 11 | 0 |
| Pending definitional units | 35 | 0 |
| Rows of the realization-stub audit | 125 | 0 |
| Definitional units with a recorded final source comparison | 0 of 5,054 | 5,054 of 5,054 |
| Unticked Theorems cells | 17 | 0 |
| Pending theorem units | 12,952 of 15,363 | 0 |
| `sorry` and project axioms in the library | 0 | 0 |
| Open COMPLAINTS.md requests of this repository without a task | not counted | 0 |

- **SC-001**: After the first task, the frontier generator exits 0 at every commit on `main`.
- **SC-002**: For any realized unit, a mathematician finds the constructing declaration and the
  source locator from the unit ID alone, through the definition index and the mapping row.
- **SC-003**: Every realization accepted in Sweep III has an independent source comparison
  (constitution M10) in its mapping row.
- **SC-004**: Milestone 2 holds before the first Sweep-IV proof of the corpus, except for theorems
  taken in under constitution M9.
- **SC-005**: Every ledger cell reaches its tick by the whole-source closure check, and no cell is
  ticked while a known invalid realization or mapping remains in that source.

## Assumptions

- The catalogues of FC01–FC17 are complete (all Catalogue cells ticked) and stay frozen.
- The generator's rules in `scripts/foundational_frontier.py` stand; a task of this feature that
  finds a rule wrong changes it with its regression test.
- A worker's host reaches the live Zotero library or another copy of the admitted source;
  otherwise the unit stays open for a host that does.
- Feature [001](../001-catalogue-inputs-for-the-cas/tasks.md) task T001 supplies the tier-1
  recipe `just loop`; until it lands, tier 1 is `flock .tmp/lean.lock lake env lean <module>`.

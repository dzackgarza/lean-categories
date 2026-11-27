# lean-categories Constitution

This file is the repository constitution: authority, authorship, intake of work, review and
engineering. [FOUNDATIONS.md](../../FOUNDATIONS.md) keeps its authority over *what* the
mathematics is. [CONTRIBUTING.md](../../CONTRIBUTING.md) keeps the contribution lessons `LC-01`
to `LC-21`; an article below cites the policy that it makes binding. Where this file and the
[kernel constitution v5.0.0](https://github.com/dzackgarza/lean-cas-dsl/blob/main/.specify/memory/constitution.md)
govern the same question, they agree; a governing document of this repository that disagrees
with either is corrected.

Article identifiers are stable. `M` articles govern the mathematics and its authority. `E`
articles are the engineering defaults.

## Core Principles

### M1. Authority over mathematical definitions, laws and abstract computational obligations

This repository is the single mathematical authority of the program. Categories, higher cells,
structural and forgetful functors, classifiers, typed constructors and families, operations,
predicates, coherences and comparison cells are declared here and nowhere else.

- Every user-facing method of the computer-algebra language must be a formal operation, section,
  functor, classifier query or composite declared here.
- The mathematical API must state the abstract computational obligations: required data and
  operations, dependent signatures, their composition, and the interface that publishes them.
  Formal laws must stay separate from what a computational implementation provides.
- No kernel, contract, leaf or test may define, extend or certify mathematics. A downstream need
  for missing mathematics is a task of this repository (M9).
- Backend independence forbids selecting installed backends, certifying their behaviour or
  narrowing mathematics to their capabilities. It does not forbid computational API design.

Sources: `AGENTS.md`, "Role in the programme: the single mathematical authority";
`README.md`, purpose; `CONTRIBUTING.md` LC-17 second paragraph; `INTENT.md`, opening section;
kernel constitution C1, C22.

### M2. Faithfulness to stated sources

- Every definition must check, clause by clause, against its cited source, Mathlib and the
  formalization corpus (LC-01, LC-03, LC-20).
- Compilation, familiar names, downstream theorems and the absence of `sorry` must not be taken
  as evidence of fidelity. Lean certifies derivations, not that a statement means the intended
  mathematics.
- The mathematical object is held fixed: a change of representation must not change the
  obligation. A requested statement must not be replaced by an easier one. A change that can
  alter mathematical content goes to the mathematician first (M10).
- A citation must carry an item key of the live library and a statement read on the page.

Sources: `CONTRIBUTING.md` LC-01, LC-03, LC-20; `AGENTS.md`, "Balance autonomous and
interactive work"; `docs/agents/citation-sources.md`.

### M3. No `sorry`, no project axioms, auditable alone

- The library must contain no `sorry`, no project-created axiom and no unchecked semantic axiom.
- It must build and pass its audits with no downstream package.
- `just test` (build, `lean-no-sorry`, vacuity audit, Mathlib lint audit, unused-variable check,
  axiom audit) is the complete gate. CI runs it as `just test-ci`.
- A red gate is diagnosed before more authoring (LC-07).

Sources: `AGENTS.md`, "Auditable as mathematics alone"; `justfile`, recipe `test`;
`CONTRIBUTING.md` LC-07.

### M4. Declaration at the generating category; inheritance by functorial composition

- An operation, property or structural fact must be declared once, at the lowest category at
  which it is generated, at its true generality (least-host ownership).
- A richer category must obtain it by composition with a structural functor. An operation row at
  a richer category is the restriction of the one owner along a stated structural route, with a
  proof that the two families agree.
- Structure belongs to the category, never to a typeclass argument on a carrier (LC-13). An
  operation exists only where its structure exists (LC-16).
- The general statement comes before any special case (LC-10).

Sources: `AGENTS.md` §10.3, §10.5 and "Monotone growth"; `FOUNDATIONS.md` Def. 7.6, Def. 45.1,
Def. 45.2, Prop. 47.1; `CONTRIBUTING.md` LC-10, LC-13, LC-16;
`LeanCategories/Catalogue/Semantics/Algebra/Catalogue/Magmas.lean`, module documentation.

### M5. Totality, domain evidence and universal numerals

- Every operation must be total on its declared domain; no `Option`-valued operation, default or
  totalizing convention (LC-14).
- Membership in a domain must be established by the domain's own registered evidence procedure;
  no consumer supplies that proof (LC-18).
- A numeral or literal must be the image of an element under a universal map (LC-15).

Sources: `CONTRIBUTING.md` LC-14, LC-15, LC-18.

### M6. Typed identity, comparison cells and chosen structure

- Constructor applications and family parameters are typed terms, never strings.
- Two parallel structural routes are identified only by a registered comparison cell, never by
  precedence or registration order.
- A chosen structure (a basis, a generating family, an enumeration, an orientation) is data. It
  must never be obtained from an existence proof.

Sources: `AGENTS.md`, "Typed identity"; `FOUNDATIONS.md` Def. 46.3; kernel constitution C5, C6.

### M7. The registry is the one source that consumers project

- The semantic registry lives in `LeanCategories/Catalogue/` (namespace `CasCatalogue`). Its rows
  enter only through `normalized_registry`.
- The schema, the validators and the registration gates of the registry are owned here. They are
  an implementation means of the mathematics and this repository changes them when the
  mathematics needs it. A gate that LC-16 or another policy requires is work of this repository.
- Every consumer (kernel, contract exporter, leaf, notebook) must read the registry at a pinned
  revision and project it. No consumer keeps a second table of meaning.
- A field that holds a meaning must hold it once. A new presentation of an existing meaning must
  extend or migrate the existing field, never copy it.

Sources: `AGENTS.md`, "The semantic registry lives here"; `README.md`, consumption stages;
`CONTRIBUTING.md` LC-16; kernel constitution C1, C4.

### M8. Search before authoring

- Every definition and every proof obligation, including a lemma inside a proof, must be searched
  before it is written: Mathlib, the formalization corpus (`python scripts/formalization_corpus.py
  search '<query>'`) and the broader ecosystem, under several formulations (LC-09).
- Zero hits do not authorize invention. A greenfield definition must relate itself to the nearest
  existing notions.
- The search record must be reproducible. Its place is the mapping row for a corpus unit, and the
  owning issue for any other work. The commit cites the record.

Sources: `CONTRIBUTING.md` LC-09, LC-19; `docs/agents/reuse-gate.md`; kernel constitution C17.

### M9. Authorship, permitted inputs and immediate intake

- Mathematics here is written by a formalization author, from the mathematical requirement and
  its sources. The author's inputs are the owning issue, the mathematics, its sources and this
  repository. Kernel source, contract source, leaf code, acceptance files, expected answers and
  generated goals are not inputs and must not shape a definition.
- A missing declaration that a consumer needs is a task of this repository. The workstream of
  that consumer does the task here, as a formalization author, under this constitution and the
  review of this repository. While it does that task it states the mathematics at its own
  generality and never shapes it to a kernel or a leaf. It does not supply the mathematics
  downstream instead.
- Such an issue is taken in at once. It must not wait for its corpus sweep, for the corpus task
  list (M11) or for the corpus-wide residue audit of LC-19. It keeps the search of M8 and the
  source comparison of M2.
- A consumer workstream enters the single work stream of this repository as follows: one Lean
  process under the lock (E10); commits by explicit pathspec of its own files (LC-06); the
  import lines in `LeanCategories/All.lean` for the modules that it adds are part of its task.

Sources: `CONTRIBUTING.md` LC-17; `AGENTS.md`, "Who writes here"; kernel constitution,
"Independent authorship and permitted inputs", C21.

### M10. Review

- Review of a definition must be independent of its author, informed by the requirement and its
  sources, actionable and correctable. The reviewer checks the definition against M2 and M4.
- A worker's report is evidence, not acceptance.
- The mathematician decides every change that alters mathematical content or research direction.
- A change that M9 forbids (shaped by a downstream input) is not accepted until an independent
  review clears it.

Sources: `TODO.md`, "Acceptance stays with the prime"; `AGENTS.md`, "Balance autonomous and
interactive work"; `CONTRIBUTING.md` LC-17; kernel constitution C20.

### M11. Definition-first work order and issue tree

- Definitions, structures, constructors, operations, predicates, functors and their semantic
  registration have priority over standalone theorems and lemmas, repository-wide, not merely
  within each subject or source. Complete the outstanding definitional layer before selecting
  independent proof work. A structural law or proof needed to construct a faithful Lean definition
  is part of that definition's obligation, not permission to pursue unrelated theorems.
- The single GitHub issue tree rooted at #1 is the cross-issue work order. Use
  `itree next dzackgarza/lean-categories` to select the next ready issue, not issue number,
  convenience, assignee, or a parallel work queue. Maintain the actual native sub-issue order
  so definition-bearing work precedes theorem/lemma-only work. Groupings order work; work units
  are leaves. Use native blockers for real prerequisites, never fabricated mathematical
  dependencies to simulate priority. On intake or a change of scope, restore definition-first
  order before selecting further work; verify with `itree tree` and `itree doctor`.
- Classify by the missing mathematical output, not the title or Lean declaration keyword.
  In a mixed obligation construct the definitions first; schedule independent proof obligations
  after the definition layer, separating genuine independent review boundaries when necessary.
  Retain the entire original mathematical acceptance obligation, including all laws and proofs.
- A Spec Kit feature (`specs/<feature>/tasks.md`) supplies the tasks and their prerequisite order
  for the selected issue. Feature 002 retains the four corpus sweeps, with all definitions before
  Sweep IV. Reconcile task order with this article; neither feature selection nor immediate intake
  (M9) authorizes bypassing ready definitions for independent proof work. `TODO.md` records closed
  nodes of the earlier corpus DAG and orders no work.
- A task of a feature that adds a declaration also adds the matching row of
  `FOUNDATIONAL_DEFINITIONS.tsv` or the corpus mapping when one exists.
- No task waits. A task that uses the result of another task follows that task: the workstream
  does it first, in the feature or the repository that owns it and in the role that it names, and
  then returns (kernel constitution C16, C21). When no task produces the result, the change that
  finds the need adds the task, with its issue in the owning repository.

Sources: owner directive (2026-11-27), feature 002, research D1; kernel constitution C21;
kernel task list, "Execution order"; `itree help model`.

### M12. Defect records and workarounds

- A mathematical issue or papercut is recorded in `COMPLAINTS.md` when it is found (LC-05). A
  missing theorem is filed with statement, searches, partial sources and dependents (LC-11).
- Every workaround carries the five-field differential analysis of LC-12.

Sources: `CONTRIBUTING.md` LC-05, LC-11, LC-12.

### M13. Evidence model

- Nothing that a leaf, a kernel or a test supplies is consulted for meaning or correctness.
- Evidence classes stay distinct and no artifact certifies itself.

Sources: `AGENTS.md`, "The evidence model"; kernel constitution C2, C10.

## Engineering Defaults

### E1. Test tiers

- Tier 1 must be the smallest set of checks that establishes correctness through the happy paths
  and the branches that matter, and it must run in seconds or minutes. For a change to the
  catalogue, tier 1 is the focused elaboration of the changed modules and of the test modules of
  the changed mechanism (for example `Catalogue/Registry/*Tests.lean`,
  `Catalogue/Semantics/EvidenceTests.lean`).
- A slow tier 1 is a defect and is repaired before more work that depends on it.
- Higher tiers add evidence: the full gate `just test`, then CI.

### E2. Test design

- A test must check externally observable behaviour through a real user story: a registry read
  as a consumer reads it, a definition used as a mathematician uses it.
- Mathematical assertions are stated through the public operations, at the owner of each
  operation (`example`, `#guard_msgs`, theorems about the registered declarations).
- No mocks, no stand-in rows, no assertion that would pass on a broken registry.

### E3. Contribution lessons

- `CONTRIBUTING.md` records each lesson as a policy with a stable alphanumeric identifier
  (`LC-nn`), grouped by subject.
- Each new or revised policy must show a defective contribution beside its replacement.

### E4. Feedback cadence

- Feedback loops of ten minutes or more must be minimized. The edit-to-result loop is tier 1.
- Long runs (`just test`, CI) are for milestones: a batch of tasks, a push, a handoff.

### E5. Platform scope

- The repository supports one platform: Linux with the toolchain of `lean-toolchain` and the
  research image `ghcr.io/dzackgarza/sage:develop`. A second platform is added only on request.

### E6. Logging

- Builds, audits and scripts must write detailed logs.
- Every test run must write a durable log file of that run inside the repository tree (LC-21),
  never only to a terminal or to `/tmp`.

### E7. Timing history

- Every test and every build step must leave a timing record with the run, the revision, the
  environment (toolchain, Mathlib revision, host) and the input (module or test).
- The records are kept in the repository and shipped with it. `scripts/build-timing.sh` is the
  present writer for Lake's per-module times (`docs/build-timings.md`).

### E8. Timing triage

- Optimization work is selected from a triage table of measured costs: operation, cost per call,
  multiplicative factors, aggregate cost, priority, remedy, remaining measured cost.
- No optimization is started from a hunch.

### E9. Construction cost

- Constructing a mathematical object must be close to instant. Expensive computation is deferred
  until it is queried, unless an explicit flag asks for it eagerly.
- Elaboration of a registry row must not dominate the cost of the mathematics it registers.

### E10. Process invariants

- One Lean process at a time on the host, through `flock .tmp/lean.lock` (`AGENTS.md`, "One Lean
  process at a time").
- Bank work in commits before a wait; verify that a process is alive before waiting on it again
  (LC-08).
- Build and probe state stays inside the repository (LC-21). `just update`, never a bare
  `lake update`.
- Git history is forward only.

## Governance

This constitution and the kernel constitution v5.0.0 bind every contributor of this repository.
A governing document of this repository (`AGENTS.md`, `CONTRIBUTING.md`, `README.md`, `TODO.md`,
`docs/agents/*.md`) that conflicts with an article is corrected to agree with it and to point to
it. `FOUNDATIONS.md` owns the content of the mathematics; this file does not amend it.

An amendment must name the article that it changes, state the old and the new obligation and the
reason, update the version and the amendment date in the same change, and reconcile the
documents that repeat the article. Mathematical changes need a mathematical justification;
implementation convenience is not one.

Versions: **major** for an incompatible change to an obligation or an authority boundary,
**minor** for a compatible addition or a substantive elaboration, **patch** for an editorial
correction that leaves the obligations unchanged.

Compliance: each feature plan states its check against every article. Review (M10) checks the
change against the articles that it touches.

**Amendment (2026-11-27, M11).** Previously feature task lists alone ordered work;
now the native issue tree orders cross-issue selection, with definitions ahead of independent
theorems and lemmas. Feature task lists retain prerequisite and source obligations. This implements
the owner’s definition-first directive without weakening mathematical acceptance.

**Version**: 3.0.0 | **Ratified**: 2026-11-25 | **Last Amended**: 2026-11-27

# Active mathematical work

## Execution DAG

The nodes below reference the full sweep obligations in this file. `Needs`
lists immediate prerequisites; an entry `A` on node `B` means `A -> B`.
These edges express the existing sweep order, not new completion claims.
The linked whole-source ledger remains the sole source of sweep completion.

| ID | Obligation | Needs |
| --- | --- | --- |
| `corpus` | [Admitted sources, editions, scope and source acquisition](#0a-corpus-v2-amendment--four-admitted-sources) | none |
| `catalogue` | [Sweep I: every source unit](#1-sweep-i--catalogue-every-corpus-unit) | `corpus` |
| `mapping` | [Sweep II: every unit's Lean route](#2-sweep-ii--map-every-unit-onto-existing-lean) | `catalogue` |
| `definitions` | [Sweep III: definitions and intrinsic laws](#3-sweep-iii--realize-the-complete-definitional-layer) | `mapping` |

The definition rows below deliberately carry no counts. They used to, and every one of them was
wrong within the day: `fc05-definitions` still read "199 pending of 376" after the source had
closed at 371 of 371, and the denominator had moved twice under classifier repairs. A count
copied into this file is a second, frozen copy of something the frontier regenerates, and a
worker reading the stale copy either redoes closed work or stops short of the real remainder.
Read the frontier.


| `track-the-catalogue` | **Blocks `remap-strict-bundle`, and everything that node blocks.** `.agents/` has zero tracked files, no `.gitignore` rule, 378 markdown files and 15 MB — the corpus catalogue and every Sweep-II mapping decision in the repository. Nothing about the artifact that decides reuse against invention for the whole corpus is in history: the 2026-09-06 sweep cannot be diffed or reverted, a re-mapping would leave no trace, and losing the directory loses every source citation this project's audit claim rests on. `FOUNDATIONAL_FRONTIER.md` is tracked and derived from these files, so the tracked report is not reproducible from the tracked repository. Decide where this belongs and put it under version control there — the working assumption is that catalogue and mapping records are durable project knowledge rather than the private agent automation `.agents/` is for, so they move to a tracked path with the frontier script's default updated to follow. Whatever is genuinely scratch stays behind under an explicit ignore rule, so that `??` on this directory never again means "unknown". **Acceptance:** every catalogue and mapping file is tracked, `git log` shows them, and a fresh clone regenerates `FOUNDATIONAL_FRONTIER.md` identically | none |
| `remap-strict-bundle` | **Blocks every definition row below.** The mapping sweep of 2026-09-06 wrote `unmatched` on rows whose clauses Mathlib supplies individually, justified as "strict bundle semantics reject … one clause/example of a bundled row, or a proper subset". That is not the rule [AGENTS.md](AGENTS.md) states, and `unmatched` is what clears a unit for repo-local invention — so the corpus has been authored where it should have been mapped. The justification appears on 240 of 325 rows in `chapter-2-schemes-fc06.md`, 183 of 188 in `chapter-4-homotopy-theory-fc07.md`, and 70 of 70 in `chapter-5-submanifolds-fc08.md`. Re-map every row carrying it, clause by clause, exhausting pinned Mathlib, current upstream, open PRs, Reservoir, discoverable Lean repositories and the atlas before any row keeps `unmatched`; record the declarations supplying each clause and the comparison assembling them. Verified starting points: `FC06-C01-U013` and `FC06-C01-U015` are `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` and `zeroLocus_vanishingIdeal_galoisConnection`; `FC06-C01-U004` and `FC06-C01-U008` are the `zeroLocus` and irreducibility lemmas in `Spectrum/Prime/Basic.lean` and `Spectrum/Prime/Topology.lean`. Work source by source: a source's definition row unblocks when its own rows are re-mapped, so do not wait for all twelve. **Acceptance:** no row carries the strict-bundle justification, and each re-mapped row names its declarations and its comparison | `track-the-catalogue`, `mapping` |
| `audit-authored-definitions` | **Needs `remap-strict-bundle` for the source being audited.** A definition already authored under a row that re-maps to a real Mathlib route is reinvention now carried in the corpus, and leaving it is worse than the original mistake because it looks audited. For each such unit, either replace the local development with the library route plus a comparison theorem, or record explicitly why the library route was rejected on mathematical grounds. `LeanCategories/AlgebraicGeometry/ProjectiveCoordinateRing.lean` is the worked example of what to look for: it returns an unbundled `Ideal` and proves homogeneity separately where `HomogeneousIdeal` carries both. **Acceptance:** each audited unit either uses the library route or carries the recorded mathematical reason it does not | `remap-strict-bundle` |
| `fc05-definitions` | Sweep III for FC05: the pending count is the `## FC05 — Definitions` section of [FOUNDATIONAL_FRONTIER.md](FOUNDATIONAL_FRONTIER.md), which is regenerated; do not read a count from this row. Close this source's definitional layer before any FC05 theorem work; each definition carries its source citation and mapping record in the same commit | `mapping` |
| `fc06-definitions` | Sweep III for FC06: the pending count is the `## FC06 — Definitions` section of [FOUNDATIONAL_FRONTIER.md](FOUNDATIONAL_FRONTIER.md), which is regenerated; do not read a count from this row. Close this source's definitional layer before any FC06 theorem work; each definition carries its source citation and mapping record in the same commit | `fc05-definitions` |
| `fc07-definitions` | Sweep III for FC07: the pending count is the `## FC07 — Definitions` section of [FOUNDATIONAL_FRONTIER.md](FOUNDATIONAL_FRONTIER.md), which is regenerated; do not read a count from this row. Close this source's definitional layer before any FC07 theorem work; each definition carries its source citation and mapping record in the same commit | `fc06-definitions` |
| `fc08-definitions` | Sweep III for FC08: the pending count is the `## FC08 — Definitions` section of [FOUNDATIONAL_FRONTIER.md](FOUNDATIONAL_FRONTIER.md), which is regenerated; do not read a count from this row. Close this source's definitional layer before any FC08 theorem work; each definition carries its source citation and mapping record in the same commit | `fc07-definitions` |
| `fc09-definitions` | Sweep III for FC09: the pending count is the `## FC09 — Definitions` section of [FOUNDATIONAL_FRONTIER.md](FOUNDATIONAL_FRONTIER.md), which is regenerated; do not read a count from this row. Close this source's definitional layer before any FC09 theorem work; each definition carries its source citation and mapping record in the same commit | `fc08-definitions` |
| `fc10-definitions` | Sweep III for FC10: the pending count is the `## FC10 — Definitions` section of [FOUNDATIONAL_FRONTIER.md](FOUNDATIONAL_FRONTIER.md), which is regenerated; do not read a count from this row. Close this source's definitional layer before any FC10 theorem work; each definition carries its source citation and mapping record in the same commit | `fc09-definitions` |
| `fc11-definitions` | Sweep III for FC11: the pending count is the `## FC11 — Definitions` section of [FOUNDATIONAL_FRONTIER.md](FOUNDATIONAL_FRONTIER.md), which is regenerated; do not read a count from this row. Close this source's definitional layer before any FC11 theorem work; each definition carries its source citation and mapping record in the same commit | `fc10-definitions` |
| `fc12-definitions` | Sweep III for FC12: the pending count is the `## FC12 — Definitions` section of [FOUNDATIONAL_FRONTIER.md](FOUNDATIONAL_FRONTIER.md), which is regenerated; do not read a count from this row. Close this source's definitional layer before any FC12 theorem work; each definition carries its source citation and mapping record in the same commit | `fc11-definitions` |
| `fc13-definitions` | Sweep III for FC13: the pending count is the `## FC13 — Definitions` section of [FOUNDATIONAL_FRONTIER.md](FOUNDATIONAL_FRONTIER.md), which is regenerated; do not read a count from this row. Close this source's definitional layer before any FC13 theorem work; each definition carries its source citation and mapping record in the same commit | `fc12-definitions` |
| `fc14-definitions` | Sweep III for FC14: the pending count is the `## FC14 — Definitions` section of [FOUNDATIONAL_FRONTIER.md](FOUNDATIONAL_FRONTIER.md), which is regenerated; do not read a count from this row. Close this source's definitional layer before any FC14 theorem work; each definition carries its source citation and mapping record in the same commit | `fc13-definitions` |
| `fc15-definitions` | Sweep III for FC15: the pending count is the `## FC15 — Definitions` section of [FOUNDATIONAL_FRONTIER.md](FOUNDATIONAL_FRONTIER.md), which is regenerated; do not read a count from this row. Close this source's definitional layer before any FC15 theorem work; each definition carries its source citation and mapping record in the same commit | `fc14-definitions` |
| `fc16-definitions` | Sweep III for FC16: the pending count is the `## FC16 — Definitions` section of [FOUNDATIONAL_FRONTIER.md](FOUNDATIONAL_FRONTIER.md), which is regenerated; do not read a count from this row. Close this source's definitional layer before any FC16 theorem work; each definition carries its source citation and mapping record in the same commit | `fc15-definitions` |
| `theorems` | [Sweep IV: remaining theorem obligations](#4-sweep-iv--formalize-the-remaining-lemmas-and-theorems) | `definitions`, and per source its own `fcNN-definitions` |

| `refactor-audit` | Audit the whole corpus for messy, disorganized or duplicated Lean and carry out the refactorings that consolidate sources of truth and restore proper mathematical ownership — one owner per definition, no parallel near-duplicates of the same object, no local restatement of something the corpus already has. The realized mathematical content and its public names need not change and should not change incidentally. **This node explodes:** every refactor the audit identifies becomes its own row here with its own `Needs`, each terminating back into this node; recurse when one contains several. A refactoring that is not a node is one nobody will do. **Acceptance:** the audit is complete and every finding exists as a node — a scheduling node, not a work node, markable skippable once the plan is fully exploded | `theorems` |
| `lint-paydown` | Pay down the linter obligations where reasonable and no further: mathlib's `#lint` suite, unused arguments, simp-normal-form, vacuity and axiom audits. Every change must improve the legibility of the statement, the ability to understand what it says, and the ability to check statically that it is the source's statement. Contorting a definition or proof only to quiet a linter is the failure mode; where it is genuinely warranted it must be judged as significantly serving that goal and the argument recorded explicitly in the commit message | `refactor-audit` |
| `bloat-audit-loop` | Terminal, and it loops rather than closing. Continually audit for unnecessary bloat, non-idiomatic Lean, proof-length reduction opportunities, and anything hand-rolled that mathlib or another dependency already provides — the reuse gate applies to finished work as well as to new. Append every finding to `COMPLAINTS.md` as it is found, and repair at least one finding in the same turn that records it. A pass that files findings and repairs none has not advanced this node, and a commit whose only content is a `COMPLAINTS.md` entry is not a unit of work. The backlog may outrun the repairs, and the audit is never declared finished | `lint-paydown` |

Within a sweep, source dependencies and traversal order come from the existing
[source manifest](.agents/references/foundational-source-corpus.md); unit IDs and
their mathematical prerequisites come from the complete source catalogues.
Use `(sweep, source-unit ID)` to distinguish a unit's successive obligations.
A theorem needed for a definition's construction is an intrinsic prerequisite
of that construction, not a back-edge requiring all of Sweep IV first.
Legacy catalogues are references, not another execution branch.

Preserve task identities and full obligations when recording dependencies.
Before changing edges, check that every ID resolves and the graph has no cycle;
select work only when its required inputs are delivered, retaining active claims.
Read [contribution policies](CONTRIBUTING.md) and record newly observed issues in
[COMPLAINTS.md](COMPLAINTS.md), linking the affected unit rather than duplicating
its worklist or completion state.

## Begin each continuation here

Read [AGENTS.md — Start here: corpus execution](AGENTS.md#start-here-corpus-execution)
before selecting work. Its execution sequence and worked failure cases apply to all
four sweep plans below. Then:

0. Check [§4a](#4a-what-limits-the-rate-and-is-worth-fixing-before-the-next-source) for
   outstanding items before claiming a source. It holds work that is not sweep work and
   that makes sweep work slow — gate tiering, the projection frontier, module granularity.
   The Execution DAG above is deliberately scoped to the four sweeps, so §4a obligations
   appear nowhere in it and a continuation that goes straight to step 1 will never select
   them. An open §4a item costs every subsequent source, so it is taken first; if all are
   closed, this step is one glance.
1. Read the current sweep's plan and the existing source handoff. Resume your claimed
   source or claim the next available source in the admitted traversal order. Start
   from the latest delivered mathematics and the next unresolved source unit.
2. In Sweep I, catalogue the complete admitted source independently of Lean availability.
   In later sweeps, read that complete catalogue before filtering by kind or route.
   Include terminology, named constructions, mixed definition/theorem units, and later
   heading and metadata formats. Reconcile source-unit identities with the selected
   work; an empty filtered list is not whole-source completion.
3. In Sweeps II–IV, read each unit's source statement and the actual candidate
   declarations before accepting a route. Compare supplied data, requested output,
   hypotheses, and laws. Treat “verified” mappings in the plans as claims to check at
   this point; reuse an existing still-valid comparison, and repair a false match in
   its current mapping record.
4. In Sweeps III–IV, implement the unit at its canonical owner. Before a definition is
   exported or consumed, compare it with the source, check intended and excluded examples, and
   finish the laws needed for the construction. Inspect the meaning of project-owned
   premises before extending them. Repair an incorrect owner and affected uses before
   continuing that dependency chain; proceed with independent work when another agent
   owns the repair.
5. Commit coherent work through the existing repository checks and continue through the
   source. Before ticking its box, return to every source unit required by this sweep,
   using the phase-specific closure rules in `AGENTS.md`. Record completion in the
   existing ledger and handoff, then take the next source without waiting for another prompt.

If an omitted unit exposes a faulty selector, revisit the coverage claims made with
that selector before declaring a new exhaustive residue. Keep the already-correct
mathematics. Apply the current sweep's own obligations: mapping can end in a supported
`unmatched` route, definitions include intrinsic laws, and independent source theorems
remain in Sweep IV.

## Where the plans live

Plans are not stored in this repository. `.agents/` is a symlink to this project's directory in
the central agent memory vault at `/home/dzack/.agent-memory-vault`, so every `.agents/...` link
below resolves in a local checkout and resolves nowhere on GitHub. `.hermes/` points at the same
directory.

The plan tree has three levels:

```
.agents/plans/
├── index.md          concept index
├── plan-dag.md       every feature, plan, phase, and task, with its dependency graph
└── features/
    └── FEATURE-<NAME>/
        ├── FEATURE-<NAME>.md          the feature: scope, ordered plans, execution records
        └── plans/
            └── PLAN-<NAME>/
                └── PLAN-<NAME>.md     one plan: status, dependencies, success criteria
```

To find plans:

- Read [plan-dag.md](.agents/plans/plan-dag.md) for the full inventory and dependency edges.
- List the features: `ls .agents/plans/features`.
- Each plan file's frontmatter carries `status`, `dependsOn`, `parents`, and `successCriteria`.
  Status is one of `unstarted`, `in-progress`, or `complete`.
- Search the vault by name or content:

  ```bash
  agent-memory search --scope project "<plan or subsystem>"
  ```

Progress belongs to two surfaces and no others: a plan's own `status`, and the whole-source
[corpus status ledger](.agents/references/foundational-corpus-status.md) for the four sweeps
below. Reference material — source catalogues, mapping records, the Lean source atlas — lives in
`.agents/references/`.

## The foundational programme

The foundational programme is source-based and corpus v1 is frozen. The exact editions,
source dependencies, prerequisite rationale, and verified Markdown extraction paths live in
[the foundational source index](.agents/references/foundational-source-corpus.md). Whole-source
progress for all four sweeps lives only in the
[central corpus status ledger](.agents/references/foundational-corpus-status.md).

The same corpus is traversed in four separate sequential sweeps:

1. catalogue every mathematical unit;
2. map every unit against existing Lean formalizations;
3. realize the complete definitional layer;
4. formalize the remaining lemmas and theorems.

Do not merge these sweeps. In particular, implementation availability must not shrink the
catalogue, and theorem formalization may be long-running without holding the definitional DSL
hostage.

## 0. Frozen foundational corpus v1

The deterministic source order is:

1. `FC01` Dummit–Foote, *Abstract Algebra*;
2. `FC02` Munkres, *Topology*;
3. `FC03` Riehl, *Category Theory in Context*;
4. `FC04` Atiyah–Macdonald, *Introduction to Commutative Algebra*;
5. `FC05` Weibel, *An Introduction to Homological Algebra*;
6. `FC06` Hartshorne, *Algebraic Geometry*;
7. `FC07` Hatcher, *Algebraic Topology*;
8. `FC08` Lee, *Introduction to Smooth Manifolds*;
9. `FC09` Neukirch, *Algebraic Number Theory*;
10. `FC10` Serre, *Local Fields*;
11. `FC11` Peters–Sterk, *Symmetric and Quadratic Forms*;
12. `FC12` Beauville, *Complex Algebraic Surfaces*.

This order was chosen by mathematical dependency and abstraction ownership, not by subject
breadth. In particular, Dummit–Foote supplies modules before Atiyah–Macdonald localizes them;
Riehl supplies categorical language before later localization/base-change/sheaf constructions
are categorically realized; Weibel supplies generic homological objects before Hartshorne and
Hatcher instantiate them; and Neukirch/Serre supply local arithmetic before Peters–Sterk's
p-adic lattice theory.

Changing corpus membership, order, edition, or bounded scope requires a new explicit corpus
version/amendment. Amendment v2 below is the only such change so far. Existing
Folland/Ahlfors/Shafarevich/Whitehead/Apostol/Lam/Gerstein/etc. catalogues remain supplementary
and do not silently enlarge the corpus.

## 0a. Corpus v2 amendment — four admitted sources

Amendment v2 admits four sources. It does not renumber, re-edition or rescope `FC01`–`FC12`, so
every existing source-unit ID stays valid:

13. `FC13` Matsumura, *Commutative Ring Theory*;
14. `FC14` Humphreys, *Introduction to Lie Algebras and Representation Theory*;
15. `FC15` Humphreys, *Reflection Groups and Coxeter Groups*;
16. `FC16` Humphreys, *Linear Algebraic Groups*.

Each closes a gap in the v1 dependency spine. None is admitted for subject breadth:

- `FC13` sits between `FC04` and `FC06`. Atiyah–Macdonald is deliberately slim, and Hartshorne
  assumes the homological commutative algebra it omits: regular sequences and depth,
  Cohen–Macaulay and regular local rings, Koszul complexes, completion, and flatness criteria.
  Matsumura owns that material instead of letting scheme theory reinvent it locally.
- `FC14` owns semisimple Lie algebras, root systems, weights, and their representation theory.
  No v1 source defines a root system.
- `FC15` owns reflection groups, Coxeter systems, and their geometric representations. The
  reflection and orbit applications in the research programme use these as primitives.
- `FC16` owns linear algebraic groups and their actions, so group actions on varieties and
  schemes reuse one owner rather than a local stand-in.

`FC13` is a prerequisite of `FC06`, so numeric ID order is no longer the traversal order. Corpus
v2 traverses:

`FC01`, `FC02`, `FC03`, `FC04`, `FC05`, `FC13`, `FC06`, `FC07`, `FC08`, `FC09`, `FC10`, `FC11`,
`FC12`, `FC14`, `FC15`, `FC16`.

Two further sources are admitted as **supplementary only**, not as corpus members: Folland,
*Real Analysis: Modern Techniques and Their Applications*, and Conway, *A Course in Functional
Analysis*. No corpus source's dependency spine passes through measure theory or functional
analysis, so neither enters the denominator of the four sweeps. Supplementary formalization
against them stays valid.

All four v2 sources have local PDFs but no verified Markdown extraction. Each needs source
acquisition before Sweep I can traverse it.

## 1. Sweep I — catalogue every corpus unit

Plan: [PLAN-FOUNDATIONAL-CORPUS-CATALOGUE-SWEEP](.agents/plans/features/FEATURE-FOUNDATIONAL-CORPUS/plans/PLAN-FOUNDATIONAL-CORPUS-CATALOGUE-SWEEP/PLAN-FOUNDATIONAL-CORPUS-CATALOGUE-SWEEP.md).

Traverse every corpus source completely, in the v2 traversal order above. Record every formal
unit:

- definitions, constructions, conventions, and notation;
- lemmas, propositions, theorems, and corollaries;
- admitted named examples/comparison statements;
- exact source location, hypotheses/data, and source-unit dependencies.

- [x] Upgrade existing definition-only catalogues into complete source-unit catalogues.
- [x] Catalogue every source without consulting Lean coverage to decide whether a row belongs.
- [x] Assign stable source-unit IDs used unchanged by all later sweeps.

Which sources are catalogued is stated only in
[the corpus status ledger](.agents/references/foundational-corpus-status.md). The catalogues
themselves are one file per source in
`.agents/references/foundational-corpus-units-fc*.md`. Each catalogue is faithful to its frozen
Markdown extraction, which no phase has yet compared against the printed source.

A source is not fully catalogued merely because all of its definitions have existing Lean
routes; its theorem/lemma content still belongs to Sweep I.

## 2. Sweep II — map every unit onto existing Lean

Plan: [PLAN-FOUNDATIONAL-CORPUS-MAPPING-SWEEP](.agents/plans/features/FEATURE-FOUNDATIONAL-CORPUS/plans/PLAN-FOUNDATIONAL-CORPUS-MAPPING-SWEEP/PLAN-FOUNDATIONAL-CORPUS-MAPPING-SWEEP.md).

Complete. Which sources are mapped is stated only in
[the corpus status ledger](.agents/references/foundational-corpus-status.md); the per-source
verdicts live in the mapping records beside it, one file per source,
`.agents/references/foundational-corpus-mapping-fc*.md`.

Take a source, not a chapter. Choose the first source in the v2 traversal order whose Mapping box
is unticked and that no other agent has named as in progress, name it at the head of its mapping
record, then map it straight through to the end and tick its box yourself. Do not stop between
chapters to be told to continue, and do not wait to be given a source.

For **every** source-unit ID, search existing Lean work before constructing any local
formalization queue.

The mandatory search surface includes:

- pinned Mathlib source;
- current upstream Mathlib, relevant source history, and open PRs;
- Loogle, LeanSearch, Mathlib docs, and the local source atlas;
- Lean Reservoir and every discoverable packaged Lean project;
- broad GitHub code/repository search across all discoverable Lean repositories, not merely the
  curated source registry;
- local mirrored/reference corpora and statement banks such as `formal-conjectures` where
  relevant.

Search standard names, source theorem names, synonyms, namespaces, and expected type/statement
shapes. Inspect candidate declarations and hypotheses; string similarity is not a match.

Each unit must end in exactly one route class:

- `mathlib` — use the canonical Mathlib declaration/proof;
- `project-existing` — use the existing canonical LeanCategories owner;
- `package-import` — import an external Lean package;
- `reference-port` — Lean code exists but is not directly importable; preserve/copy the exact
  implementation with repo/commit/path/license provenance and port/adapt it later;
- `unmatched` — no acceptable Lean implementation was found after the exhaustive search.

- [x] Record declaration names, repository/package, commit/tag, path, license,
  toolchain/Mathlib compatibility, and mathematical generality for every mapping.
- [x] Import usable packages rather than reimplement them.
- [x] Preserve non-importable Lean implementations as reference implementations rather than
  re-derive their mathematics.
- [x] Put **only** `unmatched` units into a greenfield formalization queue.

## 3. Sweep III — realize the complete definitional layer

Plan: [PLAN-FOUNDATIONAL-CORPUS-DEFINITION-SWEEP](.agents/plans/features/FEATURE-FOUNDATIONAL-CORPUS/plans/PLAN-FOUNDATIONAL-CORPUS-DEFINITION-SWEEP/PLAN-FOUNDATIONAL-CORPUS-DEFINITION-SWEEP.md).

Start only after Sweep II completes. Traverse every definitional source unit according to its
mapping:

- reuse `mathlib`, `project-existing`, and `package-import` owners directly;
- port/adapt `reference-port` implementations with exact provenance;
- author new Lean mathematics only for `unmatched` units.

- [ ] Realize every definition, construction, category, morphism class, functor, natural
  transformation, predicate, notation-bearing object, and universal construction.
- [ ] Define missing ambient categories and structural functors rather than introducing local
  stand-ins inside downstream subjects.
- [ ] Place every definition at the lowest mathematical owner that generates it.

Sweep III includes proofs intrinsic to making definitions well-defined: category/functor laws,
quotient well-definedness, independence of representatives, closure, and analogous structural
obligations. It does not absorb the source's general lemma/theorem programme.

Completion of Sweep III is the broad foundational-DSL milestone. Advanced definitional work may
draw on this vocabulary even while Sweep IV is incomplete; a consumer requiring an unfinished
theorem depends on that theorem specifically.

## 4. Sweep IV — formalize the remaining lemmas and theorems

Plan: [PLAN-FOUNDATIONAL-CORPUS-THEOREM-SWEEP](.agents/plans/features/FEATURE-FOUNDATIONAL-CORPUS/plans/PLAN-FOUNDATIONAL-CORPUS-THEOREM-SWEEP/PLAN-FOUNDATIONAL-CORPUS-THEOREM-SWEEP.md).

Start after Sweep III. Traverse every non-definitional Sweep-I unit using the Sweep-II mappings:

- reuse canonical/imported proofs;
- port external reference proofs when available;
- locally prove only the `unmatched` residue.

- [ ] Formalize every remaining lemma, proposition, theorem, corollary, and admitted comparison
  with its exact hypotheses.
- [ ] Preserve the source dependency graph rather than replacing difficult results with weaker
  local substitutes.
- [ ] Link specialist theorem programmes back to their source-unit IDs.

Sweep IV may be very long-running. Unproved theorem units remain open theorem work; they are not
encoded as axioms, theorem-shaped structure fields, weakened definitions, or reasons to narrow
Sweep III.

## 4a. What limits the rate, and is worth fixing before the next source

Neither item below is sweep work. Both are why sweep work is slow, and this repository can
only ever run one worker, so an hour spent waiting is an hour the corpus does not advance.

### `test-commit` is `test-ci`, so every commit pays a whole-project elaboration

`justfile` defines `test-commit: test` and `test-ci: test`, and `test` is `build` followed
by the exporter, `lean-no-sorry`, `_lint-conventions`, `_lean-vacuity-audit`,
`_lean-mathlib-lint-audit`, `_lean-unused-variables` and `_lean-axiom-audit` — a full
repository elaboration plus five whole-environment audits, for a commit that may have
added one definition to one file.

Measured on the productive run of 2026-09-10 21:10 through 2026-09-11 05:48, the interval
between consecutive `feat` commits was 37, 23, 24, 9, 10, 43, 13 and 41 minutes, median
about 24. Nineteen commits landed in twenty-four hours. The mathematics in each is minutes
of work; most of the interval is the gate.

The gate holds `.git/index.lock` for its whole run, so the cost is not only the waiting
worker's. Observed 2026-09-11 06:23–06:40: a commit's `lean-categories-axiom-audit` held
the lock for seventeen minutes, during which no other write to this repository was
possible — which is also the mechanism behind the stale locks `LC-05` exists for, since a
gate killed part-way through leaves that lock with no owner.

The obligation is to separate the tiers, not to weaken either. Commit tier checks what the
commit changed and its dependents; CI tier keeps the whole-environment audits exactly as
they are, since `env_linter`-backed checks like the vacuity audit are inherently
whole-environment and belong where they are paid once.

**Acceptance:** a one-declaration commit no longer elaborates the whole project, the full
audit set still runs at `test-ci`, and no audit is deleted or narrowed to achieve it.
Record the measured before/after interval in the commit.

**Delivered `8a31f94`**, and the measurement held: a one-declaration change passes
`test-commit` in **23.26 s** against a recorded ~24-minute median before, with `test-ci`
intact at 350.08 s. What follows is the next step, not a revision of that.

### What each of the three tiers is actually for

The tiers exist and are wired — `test-commit` on pre-commit, `test-push: test-ci` on
pre-push — but they are still all asking the same question, only over different amounts of
the tree. They should be asking different questions.

**The highest priority in this repository is writing the mathematics down.** A corpus of
sixteen sources is a transcription job before it is anything else, and the throughput that
matters is source units reaching the tree. Every gate is justified only by how little it
obstructs that while still keeping the tree from becoming nonsense.

- **Commit tier is a sanity check, not a quality gate.** Its job is to catch what the
  author forgot or overlooked while the context is still live and the fix is seconds:
  does this parse, does it follow the conventions, is the name what the mapping record
  says, did the unit get its ledger entry. It should be fast, and — more importantly — it
  **must not require the library to elaborate**. A worker transcribing FC05 that writes a
  definition referring to something not yet transcribed currently cannot bank it at all,
  and `lake build LeanCategories` at commit tier is what stops it. Partial, incoherent,
  in-progress state is the normal condition mid-sweep and banking it is what makes it
  survivable; `LC-04`'s "staged work is not banked work" points the same way.
- **Push tier carries the hard work.** Full elaboration, the whole-environment audits, the
  exporter, sorry-freedom. This is where 350 seconds is well spent, because it is paid once
  per batch of work rather than once per declaration.
- **The contribution gate is the guarantee to the outside world.** Anything leaving this
  repository must be coherent, compilable and of defensible quality. That is a real
  promise and it does not move.

So the remaining change is narrow: take whole-library elaboration and sorry-freedom out of
commit tier and let push tier own them, leaving commit tier the cheap checks that catch
mistakes early. This is the same trade `DEV-58` makes in the research repository, and the
same one FLT made by letting a statement be a usable node before its proof existed.

**Acceptance:** a worker can commit a partially elaborated unit mid-transcription; `just
test-push` still refuses anything that does not fully elaborate, pass every audit and
contain no `sorry`; and the commit-tier checks that remain are ones that would have caught
a real recent mistake, named in the commit.

### Corpus rework is a milestone phase, not continuous

Reorganising and reworking what has been transcribed — fixing owners, consolidating
duplicated notions, repairing mappings found wrong in hindsight — is proper work, and it
belongs in a triage phase at the end of a transcription milestone rather than interleaved
with the transcription itself. Interleaving it is what turns a sweep into an unbounded
refactor and is why a sweep can run for days without a cell closing. Transcribe to the end
of the source, then triage what the sweep exposed, then close the cell.

**How the two 2026 large formalizations handled this, since neither made the check cheap —
both made it rare.** Anthropic's FLT formalization (29,511 theorems, 60,475 modules) has a
full kernel check costing about **5 h 32 m at 96 parallel jobs**, peaking at 153 GB of
memory, with an independent comparator pass at roughly 15 hours on top. That check ran at
the end of the run, not per unit of work. Per unit of work the granularity was one theorem:
statements live in `Theorems/` and proofs in `P2M/Sol/`, each proof module importing only
the statements it cites, so proving a leaf elaborates that leaf against already-accepted
statements rather than the project. Statements were reviewed by other agents *before* proof
work began, which caught false statements while they were still cheap. The terminal gate is
a single `FinalCheck.lean` asserting

```lean
/-- info: 'fermat_last_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fermat_last_theorem
```

OpenAI's Navier–Stokes release is the same principle at small scale: `lake exe cache get`
so Mathlib is never compiled, one self-contained development, and an external
`lake exe comparator` run to certify the formalized statement matches the intended problem
statement.

Two things follow for this repository, and neither requires new machinery:

- **The root-axiom check subsumes the whole-environment scans.** An axiom collection over
  the exported root catches `sorryAx` anywhere in its dependency tree, transitively — which
  is what `lean-no-sorry` is scanning the whole environment for on every commit.
  `LeanCategories/Tools/AxiomAudit.lean` already calls `collectAxioms` from
  `Lean.Util.CollectAxioms`, so the capability exists; it is being spent per commit as a
  sweep instead of once as a terminal assertion over the roots.
- **Separating statements from proofs is what makes the commit-tier check small**, and it is
  the same restructuring the frontier item below needs in order to schedule work per unit.
  Do them together rather than twice. 297 files holding 4,417 declarations is coarse enough
  that almost any edit pulls in a large recompile; FLT's 60,475 modules for 29,511 theorems
  is the granularity that makes leaf-level checking possible.

Neither project skipped verification — FLT ran two independent external checkers, one a
separate Rust kernel. They moved the total cost out of the inner loop.

**Three things that reference architecture does not settle for us, so decide them first
rather than porting FLT's layout literally.**

*The root is already named.* `#print axioms` needs something to point at, and FLT had one
theorem. Here the analogue exists: `lake exe lean-categories-export` calls the checked
manifest path `LeanCategories.checkedRegistryManifest`, and `ExportBoundaryProbe.lean`
already `#check`s it. Whatever else changes, the terminal assertion should be over the
registry manifest and anything else the export boundary treats as a root — settle that root
set explicitly and write it down, because a per-commit sweep can be replaced by a terminal
assertion only if the assertion demonstrably covers the same declarations.

*Statement/proof separation does not transfer to a definitional corpus, and that is the
phase we are in.* This tree holds 2,752 `def`/`abbrev`/`structure`/`class`/`instance`
against 1,679 `theorem`/`lemma`, and the remaining frontier is twelve Sweep III definition
cells before sixteen Sweep IV theorem cells. A definition has no proof to split from its
statement, so FLT's `Theorems/` versus `P2M/Sol/` division buys little for the work
immediately ahead. What does transfer is the part underneath it: module granularity and
narrow imports, so that editing one declaration recompiles its module and its dependents
rather than a large component. Apply that now; revisit the statement/proof split when
Sweep IV makes this a theorem-heavy tree, where it earns its keep.

*Mathlib is not the cost.* `lake exe cache get` is wired as the `cache` recipe and
`.lake/packages/mathlib/.lake/build` holds 6.7 GB of prebuilt artifacts, so the gate is not
rebuilding Mathlib. The 644 jobs a trivial commit triggers are this repository's own
modules. That rules out the usual first answer and points the work squarely at the import
graph — `importGraph` is already a dependency and can tell you which modules a change
actually forces.

### The remaining sweep frontier is 30 whole-source cells with no finer structure

The [corpus status ledger](.agents/references/foundational-corpus-status.md) is scored per
source per sweep: 16 sources × 4 sweeps, of which 34 cells are checked. A checkbox means
the sweep is complete for the entire source, and partial chapter progress deliberately does
not check it. That is the right rule for a completion ledger and the wrong granularity for
choosing the next hour of work: FC05 Weibel definitions is a single unticked box covering a
whole book, and the twelve remaining definition cells and sixteen theorem cells are the
same shape.

Between 2026-09-10 and 2026-09-11 one cell moved. That is a true measurement of sweep
completion and a useless one for scheduling, because it cannot distinguish a source that is
nearly done from one not started, and it gives a second worker nothing disjoint to take if
this host ever has room for one.

The unit catalogues from Sweep I already hold the per-unit structure; what is missing is a
frontier derived from them — per source, which units are delivered, which are next in the
traversal order, and what each is blocked on. Derive it, do not hand-maintain it, and keep
the whole-source ledger as the sole completion authority so this does not become a second
completion claim.

**Acceptance:** a generated per-source frontier that names the next units and their
prerequisites for every unticked cell, regenerating from the unit catalogues and mapping
records. Sweep completion still reads only from the whole-source ledger.

**Completed 2026-09-11.** `8a31f94` first split the tiers: a temporary one-declaration
edit passed its incremental commit tier in **23.26 s**, versus the **about 24 min** median
interval between consecutive feature commits measured above, while the complete CI tier
passed separately in **350.08 s** on the same host/cache. The follow-up tiering change takes
the remaining library elaboration and sorry-freedom out of `test-commit`: commit now runs
only the repository's cheap local-convention scan, whose Cartan prohibition records the
actual issue #1 Corrections 2–3 failure. `test-push` still delegates to unchanged `test-ci`,
which owns full elaboration, sorry-freedom, exporter, vacuity, Mathlib-lint,
unused-variable and axiom audits.
`scripts/foundational_frontier.py` now regenerates `FOUNDATIONAL_FRONTIER.md` directly from
the canonical Sweep-I catalogues, Sweep-II mapping records and whole-source status ledger.
The current ledger has **28** unticked Mapping/Definitions/Theorems cells (12 Definitions,
16 Theorems), rather than the 30-cell snapshot recorded when this section was written; the
generated frontier follows the live ledger and does not alter its completion claims.

## 5. Legacy definition catalogues

The older per-source definition catalogues in `.agents/references/definition-catalogue-*.md` are
superseded by the Sweep-I unit catalogues. They stay as cross-checks and mapping hints. They do
not define source scope, and they never enlarge corpus v1.

The four sweep plans, frozen source manifest, and central status ledger are collected under
[FEATURE-FOUNDATIONAL-CORPUS](.agents/plans/features/FEATURE-FOUNDATIONAL-CORPUS/FEATURE-FOUNDATIONAL-CORPUS.md).
The detailed geometry gap inventory remains `PLAN-missing-prerequisite-theory-roadmap`. GitHub
issues #22 and #30–#41 continue to own live implementation dependencies, but they do not replace
the corpus-wide four-sweep programme.

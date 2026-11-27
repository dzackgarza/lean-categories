## Definitions are constructed, not deferred (2026-09-26)

This section records why the definition tail collapsed on 2026-09-25/26 and the rules that
prevent it. It governs every Sweep-III row; where older text below conflicts, this wins.

**What happened.** In 133 commits over 15 hours, 26 realized a definition. The rest cycled
rows between two shapes that each dodged constructing the object: taking the object as a
supplied parameter or hypothesis (`lieExponentialData I D` with `D` supplied; a cup product
taking its `SingularCohomologyCupData` as input; Hodge cohomology taking `hExt` as an
argument), or "selecting a candidate" whose existence was called a result obligation. Each
shape was then flagged as unfaithful and "repaired" into the other. Workers also edited the
scheduler that decides what remains: `[sweep-iii-blocked]` (added 2026-09-20 in
`scripts/foundational_frontier.py`) and later "reclassification" let rows leave the
Definitions population without being realized. Nothing compared realizations with churn.

**A definition is data and never depends on a theorem.** A theorem is stated in terms of
definitions; it can show two agree, and it can never be a prerequisite of one. When a
construction seems out of reach, what is missing is *more definitions* — the scaffolding it is
built from — or a source text that states it. Break it into those prerequisite definitions
and find or write each; transcribe a located source (acquiring a missing but useful text if
needed). Fields a Lean encoding demands — gluing compatibility, quotient descent,
well-definedness, structure laws — are part of writing the definition down: reuse or port
them, else prove them. They are engineering, not a separate phase, and never a stopping point.

**Not realizations,** and never marked `[realized]`:

- a definition taking as a parameter, instance argument or hypothesis the object it is meant
  to construct, or data from which that object is trivially read off;
- a "candidate", "selected" or specification-only value standing in for the object, with its
  existence deferred as a "result obligation";
- a row removed from the Definitions population, or marked blocked, instead of built.

**Done** means the declaration constructs the source's object from the source's inputs and a
reader comparing it with the source clause agrees; mark `[realized]` in that commit. Reuse
first — Mathlib, then the formalization corpus and importable packages — and write only what
genuinely does not exist.

**The scheduler is not the worker's to change.** `scripts/foundational_frontier.py`,
`scripts/foundational_definition_index.py`, their tests, and any marker that moves a row into or
out of the Definitions population are owner surfaces. A worker who believes a row is
misclassified files an issue for the owner and keeps working the row; it does not commit the
change.

**Check output before choosing more work.** Before each new unit run
`python3 scripts/output_check.py`. It counts, over the last 20 commits, how many realized a
definition. Below half, stop selecting units: read those commits, name the rule or constraint
being cycled on, and fix that governing text (or file it for the owner) before any further
repair. A repair of a delivered realization must cite the concrete source mismatch it fixes;
reshaping a representation without new mathematical content is churn.

`scripts/output_check.py` counts a rebuild — a `[realized]` row rewritten together with the
Lean construction that replaces a false realization — as realizing work, so the gate applies
throughout `realization-stub-audit` as well. Regenerate `FOUNDATIONAL_DEFINITIONS.tsv` inside
the commit that lands the construction; a separate selector-refresh commit is not a unit.

## Owner resume — 2026-09-16

The repository owner explicitly resumed this workstream later on 2026-09-16. The
earlier owner pause is superseded. Resume the ordinary repository execution DAG under
the one-integration-stream-per-repository rule, preserving the existing dirty/shared tree.
Preserving it means never discarding it, not leaving it unbanked: the uncommitted and
untracked modules earlier chats left behind are this stream's own work. Before starting a
new unit, bank each inherited module that elaborates and matches its frontier row, and
record in the frontier any that do not.
Disjoint delegated preparation is permitted under the construction boundary below. A later
explicit owner stop supersedes this resume; recurrence of an older scheduled pause does
not.

# Start here: corpus execution

For every request to continue the TODOs, apply this workflow before selecting or
resuming mathematical work. These instructions govern execution of the linked sweep
plans, including plans that describe their input mappings as “verified.”

1. Read the corpus task list (`specs/002-foundational-corpus-sweeps/tasks.md`) and its
   plan, the source manifest, and the whole-source ledger. Resume your claimed task;
   otherwise select the next unchecked task in the repository-wide Spec Kit execution order
   under constitution M11 and do its actual prerequisites first. Repository-wide
   definitions precede independent theorem or lemma work. Read its existing handoff and delivered declarations
   so you continue from the latest mathematical result rather than repeat a completed
   search, implementation, or integration check.
2. Establish the source's complete unit population before filtering it for the sweep.
   In Catalogue, traverse the admitted source without consulting Lean availability.
   In later sweeps, read the complete catalogue, including later heading levels,
   terminology, named examples, and mixed units. Classify mathematical content, then
   reconcile source IDs with the mapping and worklist. Resolve unparsed or ambiguous
   entries before treating the selected list as exhaustive.
3. In Mapping, Definitions, and Theorems, read the next unit's source statement before
   choosing its Lean encoding. Split mixed source rows by grammatical/mathematical role
   before doing anything else. In Definitions, compare only the source's definitional
   data, constructors, predicates, fields, notation, maps, hypotheses, and quantified
   parameters with the candidate declaration. In Theorems, compare the proposition/result
   clauses. A “verified” or “exact” mapping is usable only when the phase-appropriate
   comparison holds. Reuse an established comparison for unchanged declarations; correct
   a defeated mapping at its existing owner and preserve useful prior art. Catalogue
   establishes the obligation independently.
4. In Definitions and Theorems, implement the actual obligation at its mathematical
   owner. Check the meaning of project definitions used as premises. In the Definitions
   sweep, transcribe only the source's definitions and constructions. **There is no proof
   work in Sweep III.** If a proposed Lean representation asks the worker to prove an
   identity, law, descent statement, well-definedness theorem, existence/uniqueness claim,
   universal property, or any other proposition in order to construct the value, that
   representation is not an admissible Sweep-III route. Use the source's data-level
   presentation or a located reference definition that keeps those results separate.
   Reuse an existing formalization first.
   Repair a faulty owner and affected uses before
   extending that dependency chain. Continue independent mathematics while another worker
   owns the repair.
5. Commit coherent work using the repository's existing checks. Continue
   through the source without waiting for another “continue.” At whole-source closure,
   return to the complete population and discharge every obligation of the current
   sweep. Update the existing ledger and handoff, then take the next source. A handoff
   names the actual declarations, checks already run, and next unresolved source units
   in the existing execution record so the next worker can continue directly.

## Definitions close before theorems open

This is the project's integrity invariant, not a scheduling preference. The whole value of this
corpus is that **every definition is auditable to real literature** — a named source, a located
statement, a mapping record that some later reader can check. A corpus of Lean that merely
typechecks is worth nothing here; what makes it worth something is that each object in it is the
object the literature names.

Theorem-first work destroys exactly that. A theorem needs its objects to exist, so a worker
proving before the Definitions sweep has closed will supply the missing ones itself — inline,
plausibly, and with no source behind them. Those definitions enter the corpus carrying no
provenance and no mapping record, and nothing downstream distinguishes them from audited ones.
The corpus keeps typechecking while quietly ceasing to be an audit of anything.

It is self-reinforcing, which is why it must be prevented rather than corrected. Once theorems
depend on an invented definition, replacing it with the literature's definition means rewriting
those theorems, so every later worker finds it cheaper to keep the unaudited object and build on
it. The damage compounds in the direction of never being fixed.

The ledger shows how far this can run before anyone notices. On 2026-09-12 FC05 stood at 174/376
definitions with 202 pending, while 134/718 theorems had been delivered — hundreds of theorems
standing over a definition layer less than half built. Across FC05 through FC12 there were 1798
definitions pending against 3959 theorems.

So within a source, the Definitions sweep finishes before Theorems work begins.
Definitions contain no supporting-proof programme: the sweep writes declarations and
constructions only, with **no proof exception**. Properties and consequences of
an already formalized definition belong to Sweep IV. Examples,
counterexamples and witness constructions are theorem work and wait with the rest: a run of
commits building one counterexample — a product that fails to be epi, a witness space, an
obstruction — is deep theorem work on a single unit while the definitions its source depends on
are still missing. If a definition you need is absent, that absence *is* the next unit; add it
with its source and mapping record rather than assuming it around.

### The definitional programme is a two-state machine

There are only two substantive states before theorem work:

1. **State 1 — minimize the definitional work.** Everything in the Mapping/search DAG belongs to
   this state: bulk candidate discovery, source-ordered semantic mapping, positive-route verification,
   source/topic-batched second searches, and finally the unconstrained open-ended prior-art search.
   These tasks may fan out, repeat, or feed newly discovered repositories back into earlier mapping
   work. None of them is definition implementation. The terminal gate is
   `definition-mapping-convergence` (Milestone 1). It performs no work; it certifies that the set of
   definitions that still require ports or fresh authorship has been minimized to a fixed point.
2. **State 2 — realize the minimized definitional work.** Only after Milestone 1 closes do the
   Definitions nodes join the corpus-wide dependency-ready frontier, with source order breaking
   ties. They reuse direct owners, import packages, port references, and author only the final
   audited residue. A final corpus-wide source-conformance pass feeds
   `definition-realization-convergence` (Milestone 2). That gate likewise performs no work; it
   certifies that every definitional obligation is completely realized and source-faithful.

Do not create intermediate “milestones” for search passes. A second pass, per-source batch, or
specialist repository search is ordinary State-1 work feeding Milestone 1. Likewise a local
definition audit is ordinary State-2 work feeding Milestone 2. The milestones are state transitions,
not task buckets.

Mapping is an essential prerequisite for greenfield Definitions, but **candidate discovery is a
corpus-wide batch retrieval problem, not a source-by-source serial workflow**. Regenerate
`FOUNDATIONAL_DEFINITIONS.tsv` with `scripts/foundational_definition_index.py`; it is the derived
join of every definitional catalogue unit with its source data and current mapping. Run
`scripts/foundational_definition_candidates.py` across every row whose action is `search`, using the
live `formalization-corpus` batch operation resolved from OpenAPI. Do not issue thousands of
one-off API requests or wait for FC05 implementation before discovering candidates for FC06–FC17.
Discovery may run arbitrarily far ahead because finding prior art has no dependency on local Lean
realization. A definition already carrying `mathlib`, `project-existing`, `package-import`, or
`reference-port` is not re-searched unless concrete evidence falsifies that route.
Mapping routes record where the implementation was found at adjudication time; they are not a
post-hoc description of the current tree.  `project-existing` is reserved for a canonical
LeanCategories owner that already existed before the current unit entered Mapping.  Code authored,
ported, or imported while that source's Mapping phase is open cannot close its own mapping row and
cannot be cited as `project-existing` for that row.  Preserve accidental implementation residue,
finish Mapping from pre-existing/external evidence, and only then resume Definitions.  Likewise,
a landed `reference-port` remains `reference-port`, a landed package-backed alias remains
`package-import`, and a newly authored definition remains causally `unmatched`; realization never
erases the provenance route that justified doing the work. When a port/import/new definition is
actually accepted in Sweep III, append `[realized]` to that canonical mapping verdict. The marker is
Definition-completion state only: it does not change the route, does not count as Mapping evidence,
and must never be inferred merely from the presence of a local file. A premature or unaccepted
implementation remains residue and receives no marker.

The source traversal order governs **semantic adjudication and implementation**, not cheap
retrieval. After the global candidate census, take the first source whose definition mapping is
open, compare its candidates to the actual source clauses, and resolve every definitional row.
Positive hits receive exact provenance. A finite mandatory-surface pass may leave a row
`unmatched [negative-search-complete]`, but that is only **provisional residue** and no longer
authorizes greenfield work.

After every source's definitional mapping has received that source-local semantic pass, remain in
State 1. Run the structured second-pass DAG over the provisional residue, then run the final
unconstrained open-ended prior-art search immediately before Milestone 1. Only a survivor whose
canonical mapping record carries `[residue-search-audited]` may enter the greenfield queue. Sweep III
begins only after the Milestone-1 gate closes. Mapping of theorem/remark/example rows remains a
Sweep-II obligation but does not block that definitional state transition; those rows are resolved
before their Sweep-IV use.

Before authoring a new definition, therefore, consult the corpus-wide candidate table first, then
finish targeted searches for that unit under multiple mathematical formulations against pinned and
current Mathlib/open work, Reservoir and discoverable Lean repositories, and the other proof-assistant
repositories indexed by `formalization-corpus`. A checked Rocq, Agda, Isabelle, or other prover
implementation is still an existing reference implementation: record it as provenance to port/adapt
rather than rederive the textbook construction.

## A record update is not a unit of work

Advancing a frontier row, ticking a ledger cell, recording a mapping decision, closing a queue
item: none of these is work and none earns a commit of its own. Each one costs a full gate run
to move a marker, and a history of marker commits reads as a healthy cadence while the corpus
gains nothing. Fold the record update into the commit carrying the mathematics it describes. If
a record change has no mathematics to ride with, it is bookkeeping that should not be happening.

## The frontier is a product, and reviewing your own drift is part of the work

`FOUNDATIONAL_FRONTIER.md` and the whole-source ledger are not reports about the corpus, they
are the instruments that decide what gets built next, and they are maintained to the same
standard as the mathematics. A delivered count that does not move when work lands, a mapping
record that no longer parses, a next-units table that cannot name a ready unit: each is a
defect in the thing that selects work, and each one silently returns unit selection to whoever
is reading it. Repair it before taking the next unit, and fold the record update into the
commit carrying the mathematics it describes.

At every source closure, and whenever a session has run long without a definition landing,
look back and ask:

- **Did this session deliver units, or discuss them?** Mapping comparisons, catalogue
  reconciliation and handoff notes are part of delivering a unit; they are not a unit. A run of
  commits with no new Lean declaration in them means the session drifted into administration.
- **Did the ledger move along the dependency-ready frontier?** Sweep III definitions stay ahead of
  Sweep IV theorems because the phase boundary enforces that globally; independent definitions do
  not need an artificial serial order inside Sweep III. Source order is the deterministic
  tie-breaker among equally ready units, not a back-edge. If the earliest source-order definition
  is expensive, blocked, or waiting on an owner repair while another definition unit has all of
  its recorded prerequisites, continue the ready independent definition instead of idling the
  whole corpus behind one unit.
- **What made this source cost more than it should have?** A search you repeated, a mapping you
  could not trust, a tool that answered nothing. That is an obstruction; fix it at its owner
  and commit the fix. Working around it silently guarantees the next worker pays it again.

## Do not end a turn without the next unit started

A turn that ends on a committed definition ends the stream. Nothing restarts it until someone
outside the repository notices and asks, and the corpus gains nothing across that gap however
short it is. On 2026-09-13 this repository delivered definitions at a good rate and stopped
after each one, so most of its wall-clock went to waiting rather than to elaborating.

The unit of a turn is not one definition. Commit the definition, read the next pending unit
from the frontier, and start it in the same turn — and keep going. There is no point at which
the correct thing to do is stop and report the count: the frontier already reports the count,
and it does so more accurately than a message can.

Stop only when the frontier cannot name a ready unit, and then the scheduler is the defect
(below), not the stopping point.

## Repair the scheduler, do not route around it

The generated scheduling documents are load-bearing, and when one breaks the failure is silent:
a worker that cannot read its next unit starts choosing units itself, and the corpus drifts
toward whatever is interesting rather than whatever is next. `FOUNDATIONAL_FRONTIER.md` spent
2026-09-11 emitting its "Next 5 open units in source traversal order" heading six times with no
rows under any of them, and the workers of that night picked their own units accordingly.

So at every source closure, and whenever a scheduling document fails to answer the question it
exists to answer, stop and repair it before continuing the mathematics. Check that the frontier
tables are populated, that the ledger counts move when work lands, and that the mapping records
parse. A tool that has stopped answering is a defect to fix at its owner, never a step to work
around — the next worker inherits the same silence and makes the same drift.

The [corpus acceptance workflow](corpus-acceptance.md#corpus-acceptance-workflow) gives the detailed checks
at each of these decisions. Keep source content in the catalogue, implementation
provenance in the mapping, and completion in the existing ledger. Apply the checks as
part of doing the mathematics; they do not require a separate review programme.

## Reasoning traps to catch while executing

### A filtered list silently changes what “all” means

A catalogue contains `### U001` with `Kind: Definition`, `#### U002` with
`kind: Definition`, and U003 labeled `Terminology`. If each introduces required
vocabulary, a selector accepting only the first format omits two obligations. Finishing
its output proves completion of U001, not completion of the source.

The tempting inference is that an empty residual list means no work remains. The
mistake happened earlier, when formatting and labels became the authority for scope.
Changing a heading level does not change the mathematics. Establish all identities
first, classify their content second, and select work third. Equal totals cannot detect
different sets of IDs; another check over the same filtered input cannot recover what
that filter discarded.

### A declaration's subject is not its mathematical role

`RootPairing.IsG2` describes a supplied root pairing. It does not produce the source's
explicit G2 root-system model. Accepting it as that construction reverses the data
dependency: the missing object has become an input rather than an output.

Read the candidate's type, not just its name or nearby theory. A property can correctly
realize a source predicate. A generic construction can realize a named example without
sharing its name. An existence theorem can support a permitted choice when the required
properties and independence hold. Identify which case the source actually asks for;
reuse the complete construction when it exists and retain partial references when it
does not. Neither a familiar name nor a route label settles that comparison.

### Familiar shorthand can drop a quantified condition

A simple loop identifies its two endpoints and no other distinct parameters. Endpoint
equality plus injectivity on `(0,1)` leaves endpoint/interior collisions unchecked.
Trace two circles meeting at a basepoint: visit that point at times 0, 1/2, and 1.
Interior injectivity can hold, yet the loop is not simple. This is the missing case to
check in `LeanCategories/Topology/LinearGraph.lean` before its `IsSimpleLoop` predicate
supports `PlanarLoop.IsSimple` and orientations in `WindingNumber.lean`.

Likewise, a carrier containing a polygon's boundary may be the whole plane or just that
boundary. The containment field alone does not define the filled region needed by a
surface quotient. Read the source's region condition before relying on
`PolygonalRegion` in `LeanCategories/Topology/SurfaceSchemes.lean`.

Write the source condition with explicit quantifiers before formalizing it. Examine
relations between parts of a partition as well as relations within each part. Choose
examples from the source, so a weakened implementation cannot choose its own favourable
cases. Include an intended example to catch accidental strengthening as well as an
excluded example to catch weakening. The examples accompany the full clause comparison.

### Internal consistency can displace the source question

Lean checks the declarations supplied to it. Lemmas, imports, exports, and successful
builds can all accumulate around the wrong definition. Those successes make the current
encoding easier to trust without answering whether it expresses the source.

Keep the questions separate: first determine the source's object and laws, then check
the actual declaration against them, then use compilation and integration checks for
the delivered encoding. When a check fails, repair the representation while preserving
the obligation. When it passes, continue the mathematics from the accepted result.

### An omission can defeat a method, and a bad premise can spread

Finding one omitted terminology unit is evidence against the selection method's
completeness. Adding just that unit and resuming the same residual list preserves the
cause. Identify the failed assumption and revisit earlier closure claims that relied
on it. Preserve correct implementations while recovering the omitted obligations.

A wrong definition has a different repair boundary: its owner and semantic dependents,
including aliases, instances, exports, and mapping claims. A downstream build cannot
restore a missing condition. Repair that owner and affected uses instead of adding
consumer-specific compensations. Unrelated work remains usable and can continue.

### Sweep III construction boundary

Sweep III realizes definitions and constructions, not a theorem programme. It
records the source's data, parameters, constructors, predicates, notation, maps, and other
definitional content at the correct owner. Results *about* a constructed object —
classification, comparison, independence, universal properties beyond what the construction
itself needs — are Sweep IV. The proofs a construction's own data requires are not: gluing
cocycles and overlap compatibility, quotient descent, well-definedness of the defining map, and
the laws a structure's fields demand are part of constructing the object, and the construction
is not realized without them. Reuse or port that support first, write it otherwise. A
specification predicate or candidate data standing in for the object is not a realization, and a
definition is never `[sweep-iii-blocked]` merely because building it takes proof work.

**An unmatched top-level definition is not permission to invent its support stack.**
During realization, decompose the proposed Lean encoding into the mathematical owners it needs.
If the selected source unit would require a substantial new project-owned supporting interface,
structure, predicate, constructor, quotient model, classification surrogate, or other reusable
layer, stop before authoring that support. Treat the missing support as a newly exposed
prerequisite and run the same reuse search that guards top-level definitions: search
pinned/current Mathlib and existing project owners; importable Lean packages and the live
formalization corpus; then non-importable Lean and other proof assistants for a reference
implementation to port or adapt. Inspect the actual candidates and record exact
repository/commit/path/license provenance plus the mathematical comparison.

Prefer a direct owner, then an import, then a port/adaptation. Only after those routes fail may
the irreducible supporting residue be authored locally. The parent source unit stays blocked on
that support-search prerequisite until the route is recorded. A negative search for the parent
object does **not** justify owning lower-level mathematics that was never searched independently.

Substantial support is determined by mathematical responsibility, not line count. An invented
abstraction standing in for a missing theory, a reusable bundled data model, or a project-owned
implementation of a standard construction is substantial even when short. Thin source-specific
assembly from already justified owners is not. Every local support addition must therefore be
traceable either to an imported/reference owner or to its own reproducible negative-search
evidence and a statement of why the remaining owned code is minimal.

Defining a predicate or a structure with a law field does not require proving that law for
an instance. For example, stating the definition of a complex requires no square-zero
theorem. Constructing a particular object by a bundled API that demands square-zero evidence
does not make that evidence definition work; use a source-faithful data representation and
leave the assertion that the data satisfy square-zero to Sweep IV.
Recording formulas does not require proving their later properties; conversely, a data-only
record must contain all data that the source definition specifies.

Normal forms, identities, functoriality, existence/uniqueness, exactness, centrality,
square-zero, universality, comparison isomorphisms, well-definedness results, descent results,
and examples remain Sweep-IV work without exception. Importing a reference file does not make
its theorems part of the current task. Extract only the definitional data/construction.

Mixed source units are split by grammatical/mathematical role. Only the definitional clause
is realized in Sweep III; every proposition/result clause remains for Sweep IV. A theorem
cannot become a Sweep-III prerequisite merely because a chosen Lean encoding bundles it into
the constructor.

### Judge progress by what later mathematics can safely use

Follow the sequence from the previous handoff through delivered mathematics to its next
consumer. Preserve correct work, repair defeated assumptions, and extend sound owners.
Necessary build waits are part of delivery only while the build is alive; check that
before waiting again. Commit counts, checkbox totals, and the proportion of
administrative commits do not measure mathematical progress over time.
Repeated searches or status edits need a changed input or a concrete unresolved
obligation; otherwise resume the next mathematical unit.

### Sweep a fixed standard corpus four times

Do not discover the foundational curriculum one downstream consumer at a time. Freeze a finite,
dependency-ordered source corpus first, with exact editions/scopes and a chosen topological order
of the mathematical prerequisite graph. Then traverse the **same source-unit IDs** in four
independent sequential plans.

1. **Catalogue sweep.** Inventory every formal mathematical unit in every admitted source:
   definitions, constructions, notation/conventions, lemmas, propositions, theorems,
   corollaries, and reusable named examples/comparisons. Record exact source location, kind,
   hypotheses/data, and source-unit dependencies. Do not consult Lean coverage to decide whether
   a mathematical unit deserves a row. Establish coverage of the admitted source before
   deriving filtered worklists; unrecognized sections or metadata remain unresolved inputs.
2. **Formalization-ecosystem mapping sweep.** Only after the catalogue is complete, search every unit
   against pinned and upstream Mathlib and open Mathlib work. Then query the live
   [`formalization-corpus`](https://dzackgarza.github.io/formalization-corpus/) API as a
   first-class mandatory discovery source, not as a fallback, before continuing through
   Loogle/LeanSearch, Reservoir, the local source atlas, **broad GitHub search across all
   discoverable Lean repositories**, and the Rocq/Agda/Isabelle/other proof-assistant repositories
   indexed by `formalization-corpus`, plus local mirrors and statement banks. Inspect actual declarations
   and hypotheses. Classify the unit as
   `mathlib`, `project-existing`, `package-import`, `reference-port`, or `unmatched`, recording
   exact repo/commit/path/declaration/license/toolchain provenance. Before accepting a route,
   compare the entire source obligation with the actual candidate declarations using the
   [mapping acceptance boundary](#accept-a-mapping-against-the-whole-source-obligation).
   Import usable packages; when a checked implementation exists but is not directly importable —
   including in another proof assistant — preserve it as a reference implementation to port/adapt.
   Only `unmatched` units are greenfield mathematics.
3. **Definition sweep.** Traverse every definitional unit using its mapping. Reuse canonical
   owners directly, port reference implementations rather than rederive them, and author new
   declarations only for unmatched units. Place every notion at its correct categorical owner,
   defining any missing categories, morphism classes, functors, or universal constructions.
   Apply the narrow proof-necessity test in the
   [construction boundary](corpus-execution.md#sweep-iii-construction-boundary). Establish the
   [definition's source meaning](#establish-the-definition-before-dependent-use) before
   exporting it or building another construction on it.
4. **Theorem sweep.** Only after the definitional sweep, traverse the catalogue's non-definitional
   units, again reusing the mapping first. This is an independent, potentially very long
   programme. It must not shrink the definition sweep or delay unrelated vocabulary merely
   because a proof is hard.

Whole-source ownership and closure remain in the existing sweep record. Within Sweep III,
the coordinator may assign disjoint ready units across sources while retaining those
source responsibilities. Respect active unit/file ownership and select only units whose
prerequisite definitions/construction data are available; source order breaks ties among equally
ready work. Continue independent units when an earlier definition is unresolved.
Tick a source only after the [whole-source closure check](#close-a-source-from-its-complete-obligations)
establishes that every required unit is discharged. Unit dispatch does not narrow that
completion standard.

The corpus order itself is part of the architecture: for example modules precede localization of
modules, generic category/functor language precedes later categorical placement, and generic
homological objects precede subject-specific instances. Completion of the definition sweep is
what establishes the reusable DSL vocabulary. A consumer that genuinely uses an unproved theorem
must depend on that theorem specifically; the entire theorem corpus is not its prerequisite.

Canonical execution records:

- [corpus/foundational-source-corpus.md](../../corpus/foundational-source-corpus.md)
  owns the in-force source population: frozen FC01–FC12 plus the explicit v2/v3 amendments,
  their prerequisite order, exact editions/scopes or pinned online snapshots, and source-acquisition
  records.
- [corpus/foundational-corpus-status.md](../../corpus/foundational-corpus-status.md)
  is the single whole-source completion ledger for Catalogue, Mapping, Definitions, and Theorems.
- [`corpus/`](../../corpus/) is the repository-owned canonical home for source catalogues, Sweep-II
  mapping records, provenance contracts, and the source atlas. These are durable mathematical
  project knowledge and must remain versioned. `.agents/` and `.hermes/` are private agent-memory
  symlinks and are not authoritative for corpus state.
- [specs/002-foundational-corpus-sweeps/](../../specs/002-foundational-corpus-sweeps/) owns the
  plan and the task list of the four sweeps (constitution M11). Do not maintain competing
  per-source progress ledgers elsewhere.

### Corpus acceptance workflow

The user gesture is “continue the TODOs.” The object being advanced is the admitted
mathematical source, realized through the current sweep. Use the existing catalogue,
mapping records, Lean owners, and whole-source ledger. Apply the following checks
before the corresponding acceptance decision, not as a retrospective explanation of
a completed batch.

#### Establish the population before selecting the work

Read the complete catalogue for the source being claimed, including appendices,
tables, notation, terminology, named examples, and mixed definition/theorem units.
The source manifest determines the admitted edition and scope. Use the source-reading
gate to resolve ambiguous statements or evidence that the catalogue omitted source
content. A complete catalogue traversal does not by itself prove that its source
extraction was complete.

Identify all source-unit IDs before filtering by kind or route. Inspect actual
heading levels, metadata spellings, and table forms. A parser that accepts only
`### FCxx-` and `- **Kind:**` cannot certify a catalogue containing `#### FCxx-` or
`- **kind:**`. A whitelist containing “Definition” but excluding definitional
terminology or named constructions cannot determine Sweep III's scope.

Classify actual mathematical content. A mixed unit keeps its source ID and contributes
its definitional and theorem obligations to the appropriate sweeps. Unknown kinds,
missing metadata, duplicate IDs, unparsed records, and unread regions must be resolved
before claiming exhaustive coverage. An empty result is not proof that nothing is owed.

Classify clauses by their grammatical and mathematical role, not by adjacency to a
definition heading. A clause that introduces data, a predicate, notation, or a
construction belongs to the definition layer. A clause asserting that the introduced
object has a property is proposition/theorem content unless that property is literally
part of the source definition of the structure or predicate. Phrases such as “this
makes ... a complex”, “hence ...”, “is independent”, “is exact”, or “is an
isomorphism” do not become definition obligations merely because they occur in the same
paragraph. Descent, closure, representative-independence, and analogous assertions are propositions;
they are not definition work.

Respect the admitted source scope at the clause level. Excluded exercises do not become
additional corpus units. When adjacent source prose leaves a fact as an exercise, retain that fact's theorem role;
do not import it into Sweep III merely because it is used to discuss the construction.

Reconcile source identities with classified and mapped identities. Equal counts do
not establish equal sets, and a checker that consumes only the selector's output
cannot detect the selector's omissions. Prefer existing source-aware tooling; for a
bounded source, complete direct inspection is also valid. Do not replace failed
coverage with a sample or introduce another private residue ledger.

#### Accept a mapping against the whole source obligation

For each unit, read its full statement, hypotheses, and source context needed to
interpret it. Open the candidate declarations at the recorded revision. Compare:

- the supplied data, ambient objects, hypotheses, and quantifier domains;
- the object, map, structure, or proposition the source asks to obtain;
- defining laws, universal properties, choices, and relevant generality;
- each separate clause when the source unit bundles several obligations.

The existing mapping row must identify which declarations supply those clauses and
which comparison makes the route valid. A predicate about an already supplied object
does not construct that object. A necessary condition, special case, or collection
of ingredients is not an exact realization of the whole unit. Conversely, a generic
construction can realize a named example without a declaration with that exact name.

For calibration, compare an explicit root-system construction with
`RootPairing.IsG2`: a property of a supplied root pairing is not the construction of
the source's vectors and pairing. If a separate generic construction supplies that
model, record and use it. Do not reimplement valid library mathematics merely because
the original mapping cited the wrong declaration.

A route label or completed Mapping box is a claim to inspect, not permission to skip
the comparison. Evidence already established for unchanged pinned declarations may
be reused. If the comparison fails, repair the factual mapping at its existing owner
and preserve the original source obligation. Retain useful reference implementations
with exact provenance. Do not turn an inconvenient port or a partial match into a
greenfield task without the required reuse search.

#### Positive routes are not the current Mapping worklist

The current Mapping correction exists to eliminate unnecessary greenfield authoring. Its active
worklist is the definitional units currently labelled `unmatched`. A row already carrying a real
source route — Mathlib, an importable package, an existing project owner with recorded provenance,
or a reference implementation to port — already answers the question this correction is asking and
is left alone. Do not recursively reopen positive rows merely because their implementation chain
could be audited more deeply.

A concrete contradiction still matters: if source reading or execution shows that a positive row
does not actually implement the recorded obligation, repair that factual mapping at its owner.
That exception is evidence-driven correction, not the worklist for the current Mapping correction.
Auditing already-authored project definitions for reinvention is a separate downstream quality task.

Before Milestone 1 closes, however, run the dedicated `definition-positive-route-audit` once over
the complete positive definitional population. This is not a request to re-search already-good rows
or add ceremonial markers. Reuse existing evidence when the canonical row already records the full
source/declaration comparison; otherwise read the prose and actual declaration(s), verify every
defining clause and the claimed generality, and repair partial/name-only/false routes. Milestone 1
means both sides are finished: the positive routes are genuinely verified, and the negative residue
has survived the open-ended audit below.

#### A bundled row is matched clause by clause, and `unmatched` is the last resort

Authorship is cleared only for a unit whose mapping is `unmatched`, so `unmatched` is the most
consequential label in this repository and it is the one most easily reached by accident. A row
is `unmatched` when *every known source has been exhausted* — pinned Mathlib, current upstream,
open PRs, the live `formalization-corpus` API under multiple formulations, Reservoir, every
discoverable Lean repository, the other proof-assistant repositories indexed by the corpus, and
the formalization atlas — not when the first search returned nothing convenient.

**Negative search has two stages.** The first stage is the bounded source-local pass: read the source
obligation, query every mandatory discovery surface under the source terminology and genuinely
distinct mathematical/declaration spellings, inspect the actual candidate declarations returned,
and record dated scopes/queries plus the reason each plausible candidate fails. When that pass is
complete, the row may be marked `[negative-search-complete]` so source-local Mapping can move on.
That marker means only “all currently mandatory/indexed surfaces were exhausted”; it does **not**
authorize authorship.

Before the final audit, the DAG may run as many **structured second passes** as are useful: source-
batched searches, topic clusters, candidate-derived synonym passes, current/open upstream checks,
package-registry sweeps, or repository-specific follow-ups. These remain ordinary State-1 work. They
shrink the residue and improve its evidence, but they do not certify final absence of prior art.

The second stage is the corpus-wide **open-ended residue audit**, run only after every definitional
row has received its source-local Mapping pass and the structured second-pass DAG has converged. This
task sits immediately before Milestone 1. Assign the remaining residue to workers and explicitly ask
them to find anything that can avoid fresh definition work, without constraining them to the known
corpus, known repositories, local search engines, or the vocabulary used by earlier passes. They must
use broad repository/code search, current branches and open PRs, package registries, project histories,
web search, project/paper pages that may point to formal code, and other proof-assistant ecosystems;
they must follow newly discovered plausible repositories and names rather than treating the starting
registry as exhaustive. Search terminology can expand from candidate code, citations, author/project
names, historical nomenclature, equivalent formulations, and characteristic type signatures. A zero
result from the formalization corpus, local grep, Loogle, or GitHub alone is never enough.

The proof of that work lives in the **canonical mapping row**, not a second residue ledger. Before a
row may retain `unmatched`, the row must record enough information for another reviewer to reproduce
the search: date; the mathematical object sought; exact or faithfully summarized query formulations;
the surfaces used; revisions/snapshots where relevant; repositories/projects/branches/PRs inspected;
plausible candidates followed; and the mathematical reason each candidate fails the source clauses.
Only then add `[residue-search-audited]`. If a worker lacks access to a relevant search surface, that
surface is not silently counted as searched; the row stays open for another worker. Discovery of a
new plausible source sends the row back to semantic adjudication. Re-run the residue population until
a full open-ended pass finds no newly viable implementation/reference route.

Do not generate dozens of meaningless paraphrases merely to inflate search evidence. The audit is
open-ended in **where it looks and what new leads it follows**, not in repetitive query count. Its
termination condition is a fixed point under serious prior-art search: no newly discovered viable
owner/reference remains, and every surviving negative row has reproducible evidence of what was
actually searched.

**"No single declaration realizes the whole bundled row" is not a ground for `unmatched`.** A
source row that bundles several clauses is matched by the conjunction of the declarations that
supply those clauses, plus the comparison that assembles them; that comparison *is* the work
the row buys, and it is a fraction of the cost of a fresh development. The mapping sweep of
2026-09-06 applied the opposite rule under the name "strict bundle semantics", and the result is
in the reference tables: `chapter-5-submanifolds-fc08.md` carries it on 70 of 70 rows and
`chapter-4-homotopy-theory-fc07.md` on 183 of 188, against a Mathlib with `Geometry/Manifold`
and `AlgebraicTopology`. Spot-checked in `chapter-1-varieties-fc06.md`, `FC06-C01-U013` and
`FC06-C01-U015` are the Nullstellensatz correspondence, which Mathlib holds in
`RingTheory/Nullstellensatz.lean` as `vanishingIdeal_zeroLocus_eq_radical` and
`zeroLocus_vanishingIdeal_galoisConnection` — in the classical `Set (σ → K)` form, so the row's
own escape clause about scheme-only analogues does not apply either.

Two further grounds that are also not `unmatched`. A library declaration stated in greater
generality than the source covers the source; record the specialization as the comparison. And a
bundled type that already carries a property the source states separately — `HomogeneousIdeal`
against an `Ideal` plus a homogeneity proof — is a *better* match than an unbundled
reconstruction, not a worse one. Reaching for the unbundled form and re-deriving the property is
reinvention wearing an import.

When a mapping row is wrong, repair the row before authoring against it. A stale `unmatched`
silently converts this program from formalizing a corpus against the literature into
transcribing a textbook into Lean, and nothing downstream can tell the two apart.

#### Establish the definition before dependent use

Before writing a new definition, derive its definitional data, constructors, fields,
hypotheses, notation, maps, and quantified parameters from the source independently of
the prospective Lean encoding. Separate every proposition/result clause from that list
before implementation. Ground this in the catalogue's source unit and its mapping
record; do not create a second local account of the source.

After implementation, compare the actual declaration with that derivation. Run the
[wrong-model test](mathematical-simplicity.md#apply-the-wrong-model-test) and the
[positive and separating examples](mathematical-simplicity.md#require-one-positive-and-one-separating-example)
before adding the definition to `LeanCategories.All` or using it in another named
construction. Inspect mixed boundary cases, not only conditions within each part of
a partition. These examples are semantic reading checks, not formalization obligations
for Sweep III; do not author theorem/example proofs to satisfy them.

For a simple loop, injectivity on `(0,1)` plus endpoint equality leaves endpoint/interior
collisions unchecked. A traversal of two circles meeting at the basepoint passes that
weaker predicate. The source's equality condition must reject it before orientation
or curve theory uses the predicate. For a polygonal region, containing a polygon's
boundary alone also permits the entire plane or just the boundary; compare the source's
actual region condition before forming the intended surface quotient.

Read each imported project-owned definition whose meaning is a premise of the new
construction, or inspect its still-valid source comparison. A standard name and a
successful dependency build do not establish that meaning. Reuse canonical dependency
declarations directly once the mapping comparison establishes the match.

Apply the [construction boundary](corpus-execution.md#sweep-iii-construction-boundary) to the exact source
inputs and output. Only proof support absolutely required to formalize that definition is
admissible; other propositions and applications remain in Sweep IV.

The source comparison is not a one-time design note. After the source-order Definitions
passes finish, run the corpus-wide `definition-source-conformance` milestone: re-open the
original prose statement and the actual exported realization for every definitional unit in
the open programme. Check the complete definitional data, hypotheses, quantified parameters,
constructors, fields, notation, maps, variance, ambient category assumptions, and exact
generality claimed. For imported/reused owners, check the specialization/comparison that
makes the source notion a genuine instance. For ports and new definitions, inspect the
declaration itself. Source examples may be used to detect a wrong model, but they do not
become formal proof obligations in Sweep III. A mismatch reopens the owning definition and
every dependent realization that used the wrong meaning.

Milestone 2 closes only when this global pass finds no merely plausible, partial, weakened, or
over-specialized realization. A green build, exported declaration, no-`sorry` scan, or theorem
proved downstream is integration evidence only; none is evidence that the Lean definition
means exactly what the prose reference means.

Unresolved prerequisite definitions/construction data remain explicit dependencies. Realize
those declarations before accepting the consuming definition; continue independent ready work
while they are open. Propositions never become Sweep-III prerequisites and remain in Sweep IV.

Only after semantic acceptance should aggregate builds, exporters, and existing QC
be used as integration evidence. Targeted elaboration during implementation remains
appropriate. A build failure can require a representation repair; a build success
cannot override a failed source comparison.

#### Close a source from its complete obligations

Return to the complete source-unit population, not the last residual worklist. For
every unit carrying content required by the current sweep, identify the evidence that
discharges that phase's obligation. Reuse the existing catalogue and mapping records.
Do not create aliases or a parallel completion table to make this check easy.

Catalogue closure requires complete admitted source coverage, identities, statements,
hypotheses/data, and source-unit dependencies. Source-local Mapping closure requires an
inspected route and supporting comparison or a scoped, dated first-stage negative search
for every unit. For **definitional** work, that source-local negative result is still
provisional until the later corpus-wide residue audit. Milestone 1 closes only when every
definitional positive route is semantically accepted and every surviving negative row has
the reproducible open-ended evidence plus `[residue-search-audited]`. An admissible
negative mapping still does not require a Lean implementation in Sweep II.

Definition closure requires usable realizations of all definitional content and complete
agreement with the original prose obligation. The final definition-source-conformance pass
re-reads the source and actual realization globally after all source implementations have
landed; it is not replaced by local typechecking. Theorem closure requires the remaining
source results with their original hypotheses and conclusions proved. Do not apply an
implementation burden to Mapping, but do not weaken either definitional convergence
milestone to make an earlier box turn green.

In Sweep III, direct Mathlib/project routes need the accepted semantic match and
required reachability. Package routes need the actual accepted dependency. Reference
ports need the integrated declaration, not a downloaded file or a citation. New
mathematics needs its source-grounded declaration only; proposition/result clauses are
not Definition-sweep acceptance conditions.
For later mixed or terminology units, classification must follow their content even
when their metadata spelling differs from early chapters.

Check the source's Definitions box only when every such obligation is discharged,
required integration checks apply to the delivered revision, and no known invalidated
mapping or definition remains among those claims. This check does not require proving
the independent Sweep-IV theorem corpus. Do not infer closure from a clean worktree,
absence of `sorry`, export success, counts, or completion of the selected batch.

#### Repair the defeated assumption and its affected uses

When an omitted unit disproves an exhaustive selection, stop using that selection to
justify closure. Identify the failed assumption and revisit all previous closure
claims that relied on it. Resolve the affected population before declaring a new
exhaustive residue. Adding only the newly noticed unit leaves the selection failure
unrepaired. Preserve already correct mathematics while implementing the actual gaps.

When a source comparison or separating example disproves a definition, suspend
acceptance of its affected dependents. Trace semantic uses through definitions,
theorems, aliases, instances, exports, and mapping claims. Repair the mathematical
owner, then reconcile the dependent claims. Changing a comment, renaming the object,
or patching each consumer around the same faulty owner does not discharge the source
obligation. Do not delete or overwrite other workers' artifacts.

Continue independent work under the existing traversal rules. Ask the mathematician
only if repair requires choosing different mathematics or resolving conflicting
authorities. A failed whole-source claim does not erase valid definitions, and a
single bad definition does not make every unrelated file suspect. Restoration of a
checkbox or a passing build is not the stopping condition; restoration of the
affected source obligations is.

# Contribution policies

Use [TODO.md](TODO.md) to select work and [AGENTS.md](AGENTS.md) for the detailed
corpus acceptance workflow. [FOUNDATIONS.md](FOUNDATIONS.md) owns the mathematical
constitution. The identifiers here provide stable names for contribution rules;
the linked sections retain their full requirements.

## LC-01 — Preserve the source obligation

Apply [corpus acceptance](AGENTS.md#corpus-acceptance-workflow): establish the
complete source-unit population before filtering. Preserve every hypothesis,
quantifier, construction law, and admitted unit. Formatting and Lean availability
do not determine mathematical scope.

## LC-02 — Reuse at the mathematical owner

Apply [mapping acceptance](AGENTS.md#accept-a-mapping-against-the-whole-source-obligation).
Compare actual declaration inputs and conclusions with the source. Reuse valid
canonical owners and preserve port provenance; a property of a supplied object
does not construct the required object.

## LC-03 — Establish meaning before dependent use

Apply [definition acceptance](AGENTS.md#establish-the-definition-before-dependent-use).
Compare all defining clauses with the source, supply an intended and a separating
example, and prove intrinsic construction laws before export or downstream use.
Compilation establishes formal derivability, not fidelity to the named concept.

## LC-04 — Follow the execution DAG

Use [TODO.md's DAG](TODO.md#execution-dag) and its existing source records.
Resume valid delivered work and respect active claims. Dependencies name required
mathematical outputs, not shared filenames or preferred subject order. Preserve
all unresolved obligations and reject dangling references and cycles.

## LC-05 — Record mathematical issues and papercuts when encountered

Use [COMPLAINTS.md](COMPLAINTS.md) before leaving the affected work. Record false
statements, deficient definitions, missing constructions or maps, source ambiguity,
and concrete workflow friction, including discoveries outside the selected unit.
Give the mathematical need, observed evidence, affected owner and consumer, and
the precise uncertainty. Extend an existing entry for the same underlying issue.
Link the existing source unit or TODO owner. Recording a prerequisite defect does
not authorize using it or complete its repair; continue independent work.

## LC-06 — Preserve concurrent work and prove delivery

Read the current target before editing and preserve other workers' changes.
Commit only the intended files after inspecting their complete diff. Use existing
repository checks for implementation and the prose-only commit route for prose.
Close a source only under the [whole-source closure rule](AGENTS.md#close-a-source-from-its-complete-obligations),
with actual declarations and checks in its existing handoff.

## LC-07 — Diagnose a red gate before further authoring

The first time a commit gate, hook, or check goes red, diagnosing that failure
becomes the current task. Stop authoring; root-cause and fix the gate, or record
it as a blocker with a reproducer. Never continue authoring behind a red gate,
and never accumulate uncommitted work around one. A gate that is red on two
consecutive commit attempts is a defect to diagnose, not an environment
condition to wait out.

## LC-08 — Verify a long-running process before waiting on it again

Apply the [liveness check](AGENTS.md#a-wait-is-only-delivery-while-the-process-is-alive)
before continuing to wait on an aggregate build, the exporter, a commit gate, or
any other exec session. Find the process before interpreting its silence: no
process and no new artifacts under `.lake/build` is a dead build, not slow
progress, while a live process is progress even while it prints and writes
nothing. Restart a dead build as a stated decision, since a full aggregate
rebuild is expensive and the `.lake` tree is shared. Bank the coherent work you
already have before waiting; a staged tree is not delivery and does not survive a
killed session. Staged changes you did not create belong to the worker who
created them under `LC-06`; record a stranded staged tree under `LC-05` and leave
it in place. A gate that answers red is `LC-07`; a gate that never answers is
this rule.

## LC-09 — Search every obligation before writing it

Every definition and every proof obligation — including a lemma that appears in the middle
of a proof — is first attempted with broad searches of the formalization-corpus API
(`scripts/formalization_corpus.py`), under several formulations: the mathematical name,
synonyms and the dual notion, the Mathlib-style identifier, the key lemma names, across the
whole index (Mathlib, other Lean 4 libraries, UniMath, 1Lab, agda-categories, the AFP). A
Lean hit is imported or ported with provenance; a non-Lean hit is the reference
implementation. Only the glue between hits and the residue no source supplies is written
by hand, and the search record ships with the commit
([lean-cas-dsl specs/computational-core.md](https://github.com/dzackgarza/lean-cas-dsl/blob/main/specs/computational-core.md#cc-reuse--every-obligation-is-first-discharged-by-search-only-glue-and-residue-are-written), CC-REUSE).

## LC-10 — Work out the general mathematics before any special-case construction

Before writing a construction, comparison or proof for one instance, state the general
mathematics it instantiates and check whether that general statement already discharges it.
Stop and do this when any of the following is observed:

- **a second total category, fibration or functor is about to be defined for an object the
  repository already has in another presentation** — derive the new one from the existing
  owner instead;
- **the proof compares components of two constructions by hand** (for example, isomorphisms
  from two different sources agreeing on generators) — look first for the universal property
  or adjunction that makes the comparison unnecessary;
- **a fibration, family or construction is being assembled out of fibre-by-fibre data** —
  state it as the Grothendieck construction, straightening, pullback, composite or
  (co)limit it is, and use that theory's universal property;
- **the same kind of goal has failed twice with local tactics** — the difficulty is usually
  in the formulation, not the tactic; re-derive the statement from its general form;
- **a hypothesis appears only because the chosen presentation needs it** (for example,
  `Invertible 2` for quadratic base change) — the construction is narrower than the
  mathematics; find the general one.

Write the general statement in the owning spec or FOUNDATIONS section, with its source,
before the code. If no source supplies it (searched under LC-09), proving the general
statement at its generic owner (for category theory, `ForMathlib`) **is** the work; the
instance is then obtained from it. "Not available yet", "no second consumer yet" and
"the instance is quicker" are not reasons to build the instance first: they are the
situation this rule exists for. A construction is special-case only when it is not an
instance of any general statement, and that claim is itself stated and argued in the
owning spec.

## LC-11 — File every missing theorem in COMPLAINTS.md

A theorem or construction that an obligation needs and that the LC-09 search does not find is
never silently worked around, discarded, or recorded only in a commit message, audit or
module docstring. It is filed in [COMPLAINTS.md](COMPLAINTS.md) under `LC-05` with the
statement that is missing, the searches run, the nearest partial sources, and what depends
on it — whether it is then proved here (the entry names the proving declaration and stays
as an upstream candidate), scheduled, or left open. A route chosen *because* a theorem is
missing is itself recorded in that entry, so the detour can be undone when the theorem
exists.

## LC-12 — Every workaround carries a differential analysis

Trigger: any time an obligation reaches for something and does not find it, or finds it
insufficient, and the work then pivots — a workaround, a reframing, a detour through
another route, a drop to a special case, a weaker hypothesis, a local copy of a missing
general lemma, or a `set_option`/defeq trick standing in for missing API.

Action: the commit that lands the workaround, and the docstring of each declaration it
introduces or reshapes, state all five of:

1. **Needed** — the exact statement or construction the obligation required.
2. **Searched** — the LC-09 queries run (corpus, Mathlib, other sources) and what the
   nearest hits were, with why each is insufficient.
3. **Did instead** — what was written, and how it differs from what was needed
   (the differential: lost generality, extra hypotheses, fixed parameters, a presentation
   in place of the object).
4. **Optimal** — the reusable general solution and its generic owner.
5. **Tracked** — a `-- TODO(LC-12): …` at the workaround site naming the optimal
   solution, and the LC-11 COMPLAINTS entry that records it.

A workaround missing any of the five is incomplete work, not a documented shortcut; a
commit message alone does not satisfy (3)–(5), and a COMPLAINTS entry alone does not
explain the code at its site. When the optimal solution lands, remove the TODO and the
detour together and close the COMPLAINTS entry with the replacing declaration.

## LC-13 — Structure belongs to the category, never to a typeclass on a carrier

A distinguished element is a morphism of a named structure, and the structure is the category's:
a zero object of a category (initial and terminal); a point `1 → S` of a set, with `{0} ↪ S` a
literal subobject; the unit `1 → U(A)` of a monoid or group object `A`, reached along the
structural route from `A`'s category. These are different mathematics and are never merged.
A catalogue declaration takes its object in the category that carries the structure it uses
(`K` an object of fields, `Kⁿ` a `K`-module) and obtains each operation, unit and element along
that category's routes.

Banned: a Lean instance argument on a catalogue declaration (`[Zero X]`, `[DivisionRing K]`,
`[CharZero K]`, …) whose role is to make a literal, operation or element typecheck on a bare
carrier. Such an instance is the presentation dictating the mathematics (LC-10: a hypothesis
present because the presentation needs it); the object is taken in its category instead.

## LC-14 — Every operation is total on its domain; there are no partial maps

An operation is a morphism `D → Y` out of the object it is defined on, and nothing else. Its
domain `D` is a named object of the owning category — a subobject `D ↪ X` given by its own
definition or universal property (`GLₙ(K) ↪ Matₙ(K)`, `K^× ↪ K`, the finite subsets of `X`, the
convergent, integrable or smooth maps) — and an argument is admitted only as an element of `D`.
An argument not known to lie in `D` is a type error of the statement, found when it is read,
never a value, a failure, or an `Unknown` discovered when it is computed.

Banned, in constructions, operations, element and literal forms, registry rows, the kernel and
the language:

- partial maps in any encoding: `Option`/`Y⊥`-valued operations, `if … then some … else none`,
  a partial map classifier used to defer definedness;
- `none`, a default, `∅` or `0` returned where the thing named does not exist (a numeral `0`
  "in" `K∖{0}`, a numeral `k ≠ 0` "in" `Kⁿ`);
- relying on a total convention of Lean or Mathlib off its domain (`x / 0 = 0`, `Nat.card` of
  an infinite type, `Matrix.nonsing_inv` off `GLₙ`, `iteratedDeriv` of a non-differentiable map);
- totalising an operation by silently changing what it means (a companion matrix of "the monic
  truncation" of a non-monic polynomial);
- a fallback that re-reads or reinterprets a term so that it lands in a domain.

That an element lies in `D` is part of how the element is constructed (it is formed in `D`, or
carried there along a registered map into `D`), claimed by that construction as any law is, and
checked by tests; it is never decided at the point of use.

## LC-15 — Numerals and literals are images of universal maps

A numeral `n` of an object `R` means the image of `n` under the unique map out of the initial
object of `R`'s category (`ℤ → R` in rings, `ℕ → M` in monoids); where the category has no such
map, `R` has no numerals. A literal form is therefore a family of elements `1 → R` derived from
initiality in the owning category, not a function from `ℕ` into a carrier. That a numeral lies
in a subobject (`n ∈ K^×`, `n ∈ D`) is a proposition about that element, decided like any other;
a literal form that returns `none` to say "no such element" is banned by LC-14, and a numeral
needed in `D` is formed there, not tested for membership at the point of use.

## LC-16 — An operation exists only where its structure exists

An operation belongs to the category whose every object carries it. Inverses are group
structure: `⁻¹` is an operation of groups, so of `Mˣ` (the units functor `Mon → Grp`, right
adjoint to the inclusion), of `Aut(X)`, of `GLₙ(K) = Matₙ(K)ˣ`, of `K^×`. It is not an operation
of monoids, of `End(X)`, of `Matₙ(K)` or of a field `K`, because endomorphisms are not invertible
in general. The same holds for every operation. No endofunctor or operation may be declared on a
category some of whose objects lack the structure it uses. An element is inverted only once it is
an element of the units, formed there or admitted there with its evidence; one not established
to be invertible cannot even be written as an argument of `⁻¹`.

A row that violates this is ill-defined mathematics, and the registry must refuse it at
registration (gate owed: `lean-cas-dsl` plan node `gov-registry-gates`). Until that gate exists,
a reviewer refuses it.

## LC-17 — Formalization is authored blind to computation, tests and leaves

Mathematics here is written by the formalization author only, from the mathematical requirement
and its sources. That author never reads the kernel, the language, an acceptance test or a leaf
to decide what to write, and no agent who writes those writes here
([`lean-cas-dsl/specs/architecture.md`](https://github.com/dzackgarza/lean-cas-dsl/blob/main/specs/architecture.md),
"Authors: one role per agent"). A downstream difficulty arrives as a written request for
mathematics, and it never shapes the answer. Formalizing an API to fit what a kernel can
elaborate or a leaf can compute inverts the trust model. Such work is not accepted however it
reads: `bd31fe3` (2026-09-30) was authored this way and awaits independent review.

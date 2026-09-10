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

# Repository work documents

Read [TODO.md](TODO.md) for the execution DAG and existing sweep records,
[CONTRIBUTING.md](CONTRIBUTING.md) for named policies, and
[COMPLAINTS.md](COMPLAINTS.md) for observed mathematical issues and papercuts.
Record new issues when encountered under `LC-05`; logging never discharges the
mathematical obligation. Continue independent work whose prerequisites hold.

# Start here: corpus execution

For every request to continue the TODOs, apply this workflow before selecting or
resuming mathematical work. These instructions govern execution of the linked sweep
plans, including plans that describe their input mappings as “verified.”

1. Read `TODO.md`, the current sweep plan, the source manifest, and the whole-source
   ledger. Resume your claimed source; otherwise claim the first available source in
   the admitted dependency order. Read its existing handoff and delivered declarations
   so you continue from the latest mathematical result rather than repeat a completed
   search, implementation, or integration check.
2. Establish the source's complete unit population before filtering it for the sweep.
   In Catalogue, traverse the admitted source without consulting Lean availability.
   In later sweeps, read the complete catalogue, including later heading levels,
   terminology, named examples, and mixed units. Classify mathematical content, then
   reconcile source IDs with the mapping and worklist. Resolve unparsed or ambiguous
   entries before treating the selected list as exhaustive.
3. In Mapping, Definitions, and Theorems, read the next unit's source statement before
   choosing its Lean encoding. Compare the candidate's actual inputs, output,
   hypotheses, and laws with every clause of that statement. A “verified” or “exact”
   mapping is usable only when that comparison holds. Reuse an established comparison
   for unchanged declarations; correct a defeated mapping at its existing owner and
   preserve useful prior art. Catalogue establishes the obligation independently.
4. In Definitions and Theorems, implement the actual obligation at its mathematical
   owner. Check the meaning of project definitions used as premises. Before exporting
   a new definition or building on it, compare its clauses to the source, try an
   intended example and a nearby excluded example, and complete its intrinsic
   construction laws. Repair a faulty owner and affected uses before extending that
   dependency chain. Continue independent mathematics while another worker owns the
   repair.
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

So within a source, the Definitions sweep finishes before any Theorems work begins. Examples,
counterexamples and witness constructions are theorem work and wait with the rest: a run of
commits building one counterexample — a product that fails to be epi, a witness space, an
obstruction — is deep theorem work on a single unit while the definitions its source depends on
are still missing. If a definition you need is absent, that absence *is* the next unit; add it
with its source and mapping record rather than assuming it around.

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
- **Did the ledger move, and in source order?** Units delivered out of order are drift even
  when each one is correct, because the order is what keeps definitions ahead of the theorems
  that depend on them.
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

## Write Lean sources with the patch tool, not a shell heredoc

Writing a whole file with `cat > Foo.lean <<'EOF'` fails here, and it has failed thirteen times
in this chat against zero failures across the other three managed repositories, which do not
write Lean. Each failure costs the turn that produced the file and a reformulation; the recovery
every time was the patch tool, which wrote the same content without complaint.

So create and edit `.lean` files with the patch tool. Use the shell for what it is good at here
— `rg` over mathlib, `lake env lean` on one file, reading a range out of a dependency — and not
for delivering source text through a command string.

If a heredoc write does fail, do not retry it and do not shorten the file to make it fit: switch
tools and keep the definition intact. A definition trimmed to survive a write path is a worse
definition, and nothing downstream records why it shrank.

## Bank before you wait

Work that is written but uncommitted lives only in this chat's working tree, and a turn that
ends, a chat that is replaced, or a host that runs out of memory takes it with it. On
2026-09-13 this repository sat idle holding several tracked paths of finished repairs, none of them
banked, while the thing they were waiting on was an elaboration that had not returned.

So order the work the other way. When a piece is written and you believe it correct, commit it
*before* starting whatever comes next — the validating run, the next collection, the rest of
the batch. A commit is not a claim that everything is finished; the message can say what is
still pending. What it buys is that a stall, a kill or an ended turn costs a wait and nothing
else, rather than taking the work with it.

Commit in coherent groups as you go, not in one batch at the end. One definition elaborated is a commit; a batch of them waiting on a single `lake` run is a batch that one failed run can cost you entirely.

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

The [corpus acceptance workflow](#corpus-acceptance-workflow) gives the detailed checks
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

### Phase labels do not decide what a construction owes

A quotient needs representative independence to define its map. A category needs its
composition laws. A normal-form construction needs the property making its output
normal. These are intrinsic definition work even when Lean expresses them as theorems.
General classification results can remain in Sweep IV. Discharge an exact prerequisite
theorem when a construction needs it, without absorbing the surrounding theorem corpus.
Conversely, an admissible unmatched route can finish a Mapping obligation without yet
implementing it. Apply each sweep's own completion condition.

### Judge progress by what later mathematics can safely use

Follow the sequence from the previous handoff through delivered mathematics to its next
consumer. Preserve correct work, repair defeated assumptions, and extend sound owners.
Necessary build waits are part of delivery only while the build is alive; check that
before waiting again. Commit counts, checkbox totals, and the proportion of
administrative commits do not measure mathematical progress over time.
Repeated searches or status edits need a changed input or a concrete unresolved
obligation; otherwise resume the next mathematical unit.

### One Lean process at a time — a second one gets both killed

A single `lean` elaborating a non-trivial file holds one to two gigabytes here, and this
host has under eight in total with a browser and three other repositories' workers on it.
Two concurrent checks is already over the line: on 2026-09-11 `check-sigmaext.lean` at
1.75 GB and `test-ag-ringfull.lean` at 1.20 GB ran together alongside a 0.65 GB toolchain
process, the machine went to 125 MB free, and the kernel took the longest-running one.

That is the mechanism behind the stale index locks. A gate killed part-way through leaves
`.git/index.lock` with no owner, the next commit attempt fails on it, and the repository
becomes uncommittable for every stream until someone proves the lock stale and moves it
aside. The visible symptom is a worker that cannot bank for hours; the cause is two
processes that should never have been running at once.

Before starting a `lake build`, `lake env lean`, or any gate that elaborates, check that
no other Lean process is running and that the machine has room for one:

```bash
pgrep -a -x 'lean|lake'        # expect nothing, or one you started and are waiting on
free -m | sed -n 2p            # available column, not free
```

If another Lean process is running, wait on it rather than adding a second — including
your own earlier one that you may believe has finished. If memory is already tight,
say so and wait; a gate started into 125 MB of headroom does not finish, it dies, and it
takes the index lock down with it.

### A wait is only delivery while the process is alive

An aggregate `lake build` prints `4760/4761` and stops. Hours later the transcript
still reports waiting on that build and declines to start a duplicate run. In fact no
`lake` process exists and nothing has been written under `.lake/build` since that line
printed: the build was killed, and the exec session that owned it died with it. On a
shared host, memory pressure, a full disk, and a dropped connector session all end a
long build the same silent way. A worker cannot see its own killed process from inside
its transcript: the poll loop looks the same whether the build is grinding or gone, so
the absence of an error is not evidence of progress.

Before continuing to wait on any long-running process — an aggregate build, the
exporter, a commit gate, or any other exec session — find the process before you
interpret its silence:

```bash
pgrep -a -x 'lake|lean'                       # the driver process
ps -o pid,etimes,times,pcpu,args --ppid <pid> # the worker child; its CPU must advance
find .lake/build -type f -mmin -5 | head      # artifacts written in the last 5 min
uptime; df -h /; free -g                      # the load, disk, and memory a restart joins
```

No process and no new artifacts is a dead build that will never return, whatever the
last line printed. A live process is progress even when it prints nothing and writes
nothing: this repository's gate runs for hours, and its exporter and audit stages
re-elaborate for long stretches without touching `.lake/build`. Read that case off the
process, and read it off the right one: `lake exe` runs the built binary as a child, and
the `lake` wrapper holds a flat CPU time for the whole stage while that child does the
work. Cumulative CPU time (`times`) advancing between two checks is work; keep waiting.
Silence is evidence only once the process is gone.

Restart a dead build as a stated decision, never as a silent retry: a full aggregate
rebuild is expensive and the `.lake` tree is shared, so say that you are starting one
and what it costs at the current load. When another worker's build is already running,
wait on theirs instead of adding a second. A gate that answers red is `LC-07`; a gate
that never answers is this rule.

Staged work is not banked work. Do not hold a staged tree across a build wait. The
commit is what survives a killed session; a session that dies holding staged files
leaves them with no record of what they were meant to prove. Commit the coherent unit
you already have, then wait. Staged changes you did not create belong to the worker who
created them under `LC-06`: do not commit, unstage, amend, or revert them to clear your
own path, and commit by explicit pathspec so a shared index cannot carry them in.
Record a stranded staged tree under `LC-05` with its file list and leave it in place.

<!-- agent-memory:start -->
# Agent memory

This repository uses the central agent memory vault at `/home/dzack/.agent-memory-vault`.

Project memory key: `projects/github.com__dzackgarza__lean-categories/index`.

Repository `.agents` and `.hermes` paths are symlinks to the same vault-owned project directory.

Before changing architecture, search both project and global memory:

```bash
agent-memory search --scope both "<task or subsystem>"
```

Record durable repo-specific lessons with:

```bash
agent-memory add --scope project --type decision --title <title> --content <content>
agent-memory add --scope project --type trap --title <title> --content <content>
agent-memory add --scope project --type advice --title <title> --content <content>
agent-memory add --scope project --type context --title <title> --content <content>
agent-memory add --scope project --type reference --title <title> --content <content>
```

Plan work is card-backed. Create and update plan cards with `agent-memory plan add` and `agent-memory plan update`, not `agent-memory add --type plan`.

Use `agent-memory retrieve <key>`, `agent-memory update <key>`, and `agent-memory delete <key>` for memory CRUD.

The vault should be committed at all times. Treat staged or unstaged vault changes as an ephemeral error state. Before normal memory work resumes, load the bundled vault-maintenance skill with `agent-memory maintain skill vault-maintenance` and follow its referenced check, repair, and commit workflows.

Move reusable lessons during maintenance with:

```bash
agent-memory maintain move <key> --to global/advice
```
<!-- agent-memory:end -->

# Goal-integrity routing (always-on)

<!-- Verbatim copy of the global section in ~/ai/AGENTS.md (authoritative); keep in sync. -->

Substituting a proxy for the goal and then optimizing the proxy — the goal
source, an error count, a reviewer verdict, a "blocked" label, metadata
self-consistency — is a cognitive failure, not a chosen one: from inside it
feels like diligence, and introspection does not detect it. So no rule below
asks you to judge your own intent. Each names an observable condition; when
the condition holds, perform the reground act — especially when the current
work feels productive, because the feeling is not evidence. Explaining or
agreeing with these rules is also not evidence: a condition that fires binds
regardless of the account you can give of it.

**The reground act:** stop and state (1) the user's original goal in the
user's own words, (2) the artifact or number the current action improves, and
(3) whether improving (2) IS (1). If it is not, act on (1), or send the user a
one-message report explaining exactly why that is impossible.

- **You are about to edit the goal source** (the TODO, plan card, issue body,
  or acceptance criterion that defines your goal) for any reason other than
  recording completion the delivered artifact itself proves, or explicit user
  instruction in the current session. From inside this feels like tidying a
  stale document; from outside, deferring, relabeling, splitting, or
  re-scoping an item you were asked to finish changes the problem instead of
  solving it. The goal source is read-only while you execute it: perform the
  reground act, then do the work or send the report.

- **A work unit has passed about two review rounds, or an hour, without a
  landed falsifiable artifact.** From inside, another reviewer, audit, or
  repair cycle feels like rigor; in cost it is the most expensive failure
  available, while pausing costs nothing. Stop and report the unit as
  mispriced instead of adding apparatus.

- **You are about to call an item hard, research-scale, or worth deferring.**
  A difficulty intuition is a stale prior. First read the repo's recent git
  log for comparable completed work; if comparable items landed in hours, this
  item is hours.

- **You re-measured a corpus-wide scalar (total error, test, finding, or
  checkbox count) a second time inside one work unit.** Whatever the intent,
  the number is now functioning as the target. Perform the reground act, write down the actual
  claim the edit makes true, and verify that claim on a concrete specimen. An
  edit justified only by the number moving is unjustified, and moving a
  checker's number by asserting something false is strictly worse than the
  original error. Re-running the specimen's own check to verify the claim is
  required verification, not a trigger.

- **You are about to declare the goal blocked.** From inside, repeated silence
  reads as mounting confirmation of an impasse; it is only the absence of a
  reply, and your own unanswered messages and automatic continuations cannot
  accumulate into evidence. Re-read the mandate first: authority already
  delegated IS the approval you are waiting for. Pausing on a genuine question
  only the user can answer is correct; silence is not such a question.

- **A reviewer finding is about to block work outside its own unit, or a
  second consecutive review round adds no new falsifiable content.**
  Acceptance is a falsifiable statement about the work itself, never a
  verdict. Record and defer out-of-unit findings; on a content-free second
  round, reground against the unit's own acceptance statement.

- **The previous turn produced only administrative artifacts (plans, audits,
  status edits, registries, validation of validation) and this turn is about
  to do the same.** From inside, organizing the work feels like progress on
  it. Perform the reground act before continuing.

# Mathematical Simplicity as Architecture

## A long-horizon orientation document for agents working on the Lean foundations, Sage bridge, and mathematical DSL

**Status.** This is an orientation and knowledge-transfer document. It is not a replacement issue plan, an implementation specification, or an adjudication of every technical claim made during the attached conversations. The conversations are a derivation record: many individual proposals were corrected or superseded. This report extracts the stable project vision, the recurring modes of agent failure, and the style of mathematical reasoning repeatedly taught through those corrections.

The central claim is simple:

> The project is trying to reduce mathematical and implementation complexity by placing the work inside a sufficiently general, standard higher-categorical framework. Agents repeatedly mistake that generality for additional complexity, then replace it with local engineering devices that solve an early symptom while making the long-term programme harder.

The correct measure of progress is therefore not the quantity of code, metadata, registries, wrappers, issue decomposition, or locally completed examples. It is the amount of accidental freedom removed by a uniform mathematical construction.

---

## 0. The one-page orientation

The programme has three coupled outputs:

1. **A Lean-owned mathematical foundation** in which categories, higher categories, classifiers, functors, higher cells, limits, categories of structured objects, and their coherences have principled definitions.
2. **A Sage correspondence** that maps Sage’s empirical category system and algorithms into that normalized mathematical universe without making Sage’s labels, parent graph, or implementation accidents authoritative.
3. **A computational mathematics DSL** in which a mathematician introduces and interrogates objects by ordinary mathematical membership and notation, while the formalization and backend routing remain invisible.

The long-term universe is not chosen only for the first algebraic examples. It must be capable of housing ordinary algebra, monoidal categories, categories of functors, sheaves, schemes, stacks, derived and spectral constructions, and computations such as loop objects and general limits. A narrow 1-categorical spike can be a model or experiment, but it is not the semantic horizon.

The conceptual compression is:

- structures and axioms are represented by **classifier morphisms**;
- an assertion that an object has structure is a **lift**;
- transport is **pullback or homotopy pullback**;
- several compatible structures are imposed by a **limit**;
- comparisons are **higher cells**;
- equations and coherence are imposed through **operation-built diagrams and fillers**;
- a named special object is usually a **value of a generic functor**, not a new primitive;
- a theorem is generally a **factorization, lift, or comparison**, not data baked into a definition;
- computation is inherited along the same functorial structure, not organized in a second user-visible mathematical universe.

This is why higher category theory is present. It gives every comparison, compatibility, choice, and coherence a standard mathematical home. Refusing that level does not remove the data; it forces the data to reappear as labels, route tables, duplicated nodes, hand-maintained composites, capability flags, or informal prose.

The repeated alignment question is:

> Is the proposed object, morphism, theorem, computation, or piece of metadata being expressed at the lowest level at which it is generated, inside a framework broad enough that later phases remain instances rather than refactors?

## How to learn the reasoning in this document

The rules below are compressed conclusions. A learner cannot apply them merely by reading them.

Do not test a learner with a slogan before teaching the distinction inside that slogan.

Use this sequence for each new distinction:

1. Show one small worked example.
2. Name each choice made in the example.
3. Change one choice while preserving the mathematical object.
4. Contrast the example with a nearby wrong case.
5. Ask the learner to explain what changed and what remained fixed.
6. Give a similar example with fewer prompts.
7. Ask for transfer to a different mathematical subject.
8. State the general rule only after the examples support it.

Do not ask, “Did you preserve the mathematical object?” That question assumes the learner can already identify it.

Ask observable questions instead:

- Which symbols name data?
- Which symbols name chosen coordinates or presentations?
- Which parts change after a basis change?
- Which equation compares the two presentations?
- Which definition still makes sense after the presentation disappears?
- Which theorem is needed to pass from one presentation to another?

### First worked example: a linear map and its matrix

Let (T : V 	o V) be a linear map. Choose a basis (e), which gives a matrix (A).

Choose another basis (e'). The matrix changes to (A' = P^{-1}AP). The map (T) does not change.

Walk through these questions:

1. What is the object? The linear map (T).
2. What is the chosen presentation? The basis (e) and matrix (A).
3. What changes? The entries of the matrix.
4. What remains fixed? The linear map and its basis-independent properties.
5. What connects the presentations? The change-of-basis matrix (P).
6. Which matrix predicates are invariant under conjugation?
7. Which predicates describe only one displayed matrix?

Now repeat the exercise with a module and a chosen basis.

Then repeat it with a group and a chosen presentation.

Only after these examples introduce the rule:

> Keep the mathematical object fixed. Change the representation, not the obligation.

### Second worked example: finding mathematical ownership

Let (M) be a finite torsion (R)-module with a bilinear form (B).

Define the (P)-primary part using (P^n x = 0).

Now temporarily erase (B).

The primary part and module decomposition still exist. Therefore, module theory owns those constructions.

Restore (B). Ask what new statement now becomes possible.

The new statement is orthogonality between different primary parts. Formed-module theory owns that compatibility.

This example teaches ownership through removal and restoration. It does not require the learner to recognize ownership in advance.

### Fade the support

Give complete answers for the first example.

Give only the questions for the second example.

For the third example, ask the learner to create the comparison and a near-miss case.

Do not confuse intelligence with prior internalization. Reduce support only after the learner demonstrates transfer.

---

## Hold the mathematical object fixed

Your first duty is not to make Lean accept code. Keep the mathematics unchanged while you find its formal expression.

Begin with the mathematical object. Identify its category, morphisms, functors, and universal properties. Only then choose a Lean representation.

When Lean resists, do not negotiate with the theorem. The resistance can expose an unclear assumption, construction, or categorical home. Return to the mathematics.

Do not replace an object with information obtained after forgetting structure. A shadow can help prove a theorem. It cannot replace the theorem.

An underlying equivalence does not identify structured objects. A module map does not automatically become a formed morphism. Prove the required lift at its proper level.

Partial work is legitimate when its limits remain visible. State exactly what you proved. Keep the stronger obligation open. Never give a partial result the completed theorem's name.

### Build the mathematical language before the target

An advanced target is not ready when the repository cannot state its definition.

Decompose the target through its definitions. Repeat this work for each missing object, morphism, predicate, functor, and universal construction.

Continue until each leaf already exists or becomes explicit foundational work. This recursive decomposition can be most of the research.

A period domain needs prior language for signatures, scalar extension, isotropic vectors, and orthogonal groups. Its name supplies none of this.

Likewise, a moduli object needs its schemes, morphisms, local conditions, and families. A declaration name cannot replace these foundations.

Keep a high-level plan as a horizon when useful. Add prerequisite plans below it before implementation starts.

A floating declaration with an advanced name is not a partial formalization. It is an unsupported assertion about an undefined object.

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
2. **Lean-ecosystem mapping sweep.** Only after the catalogue is complete, search every unit
   against pinned and upstream Mathlib, open Mathlib work, Loogle/LeanSearch, Reservoir, the local
   source atlas, **broad GitHub search across all discoverable Lean repositories**, local mirrors,
   and statement banks. Inspect actual declarations and hypotheses. Classify the unit as
   `mathlib`, `project-existing`, `package-import`, `reference-port`, or `unmatched`, recording
   exact repo/commit/path/declaration/license/toolchain provenance. Before accepting a route,
   compare the entire source obligation with the actual candidate declarations using the
   [mapping acceptance boundary](#accept-a-mapping-against-the-whole-source-obligation).
   Import usable packages; when Lean code exists but is not directly importable, preserve it
   as a reference implementation to port/adapt. Only `unmatched` units are greenfield mathematics.
3. **Definition sweep.** Traverse every definitional unit using its mapping. Reuse canonical
   owners directly, port reference implementations rather than rederive them, and author new
   mathematics only for unmatched units. Place every notion at its correct categorical owner,
   defining any missing categories, morphism classes, functors, or universal constructions.
   Prove what is intrinsic to well-definedness and categorical laws. Establish the
   [definition's source meaning](#establish-the-definition-before-dependent-use) before
   exporting it or building another construction on it.
4. **Theorem sweep.** Only after the definitional sweep, traverse the catalogue's non-definitional
   units, again reusing the mapping first. This is an independent, potentially very long
   programme. It must not shrink the definition sweep or delay unrelated vocabulary merely
   because a proof is hard.

A sweep is claimed and finished by whole source, never dispatched one chapter at a time. Take the
first source in traversal order whose ledger box for this sweep is unticked and which no other
agent has named as in progress; name it in that sweep's record before you start, so a second
agent working the same sweep takes a different source. Then work it through to the end, chapter
after chapter, without pausing between chapters to be told to continue, and tick its ledger box
yourself only after the [whole-source closure check](#close-a-source-from-its-complete-obligations)
establishes that the current sweep's obligations are discharged for every required unit.
Take the next source the same way. Nothing outside this repository knows which chapter comes
next, and no agent needs to be handed one: the ledger, the traversal order, and the mapping
records already say it.

The corpus order itself is part of the architecture: for example modules precede localization of
modules, generic category/functor language precedes later categorical placement, and generic
homological objects precede subject-specific instances. Completion of the definition sweep is
what establishes the reusable DSL vocabulary. A consumer that genuinely uses an unproved theorem
must depend on that theorem specifically; the entire theorem corpus is not its prerequisite.

Canonical execution records:

- [corpus/foundational-source-corpus.md](corpus/foundational-source-corpus.md)
  freezes FC01–FC12, their prerequisite order, exact editions/scopes, and verified local Markdown
  extraction paths.
- [corpus/foundational-corpus-status.md](corpus/foundational-corpus-status.md)
  is the single whole-source completion ledger for Catalogue, Mapping, Definitions, and Theorems.
- [`corpus/`](corpus/) is the repository-owned canonical home for source catalogues, Sweep-II
  mapping records, provenance contracts, and the source atlas. These are durable mathematical
  project knowledge and must remain versioned. `.agents/` and `.hermes/` are private agent-memory
  symlinks and are not authoritative for corpus state.
- [.agents/plans/features/FEATURE-FOUNDATIONAL-CORPUS/](.agents/plans/features/FEATURE-FOUNDATIONAL-CORPUS/)
  owns the four sequential plans and their handoff/output conventions. Do not maintain competing
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

#### Authoring is part of closing a row, when the row records what it was assembled from

The remap blocks definition work, and that block would be unsatisfiable if it also forbade the
authoring a remap concludes is necessary: a row cannot be closed as genuinely unmatched without
producing the thing it says is missing. So writing a declaration *as the resolution of the row
being remapped* is remap work, not a breach of the block.

What separates it from the reinvention this whole effort exists to undo is the row. A closed row
must name the library pieces the new declaration is assembled from. On 2026-09-13 `FC06-C02-U151`
and `U152` left `unmatched` for `project-existing` naming `LeanCategories/Schemes/Divisors.lean`,
and each recorded its route underneath — `Order.coheight`,
`Scheme.ringKrullDim_stalk_eq_coheight`, `IsRegularLocalRing` for the first, and mapped `U151`
plus `IsNoetherian`, `IsIntegral`, `Scheme.IsSeparated` for the second. That is Hartshorne's
standing hypothesis `(*)` expressed as a conjunction of Mathlib predicates, which is formalizing
a bundled source condition, not rebuilding what the library already has.

A `feat(...)` commit during the remap is therefore judged by the row it closes, never by its
subject line. With the pieces named, it is the remap finishing a unit. Without them, it is the
old failure wearing a new commit message, and the row is the only place that difference is
visible.

#### `project-existing` is not a route unless the project code is itself mapped

The audit claim of this repository is that every definition traces to real literature or a real
library. A `project-existing` row points at our own Lean file, so it only preserves that claim if
the declaration it names carries its own route — to Mathlib, to a cited port, or to a source unit
realized under these rules. Where it does not, the chain terminates inside our own invention and
the row records reinvention as though it were reuse. That is worse than `unmatched`, because
`unmatched` at least announces that something must be built.

On 2026-09-13 the FC06 tables moved `FC06-C01-U001` and `FC06-C01-U011` from Mathlib routes onto
`project-existing` pointing at `LeanCategories/AlgebraicGeometry/AffinePointSpace.lean` and
`ClassicalVariety.lean`, for units Mathlib supplies through `Fin n → k` with
`MvPolynomial.zeroLocus`, and through `IsIrreducible`/`IsClosed`/`IsOpen`. Nothing in the rows
was false; the files exist and do contain the constructions. The rows were still wrong, because
the question a mapping answers is not "does this repository have it" but "what does this
repository owe the literature for it".

So before recording `project-existing`, open the named declaration and find its own route. If it
has none, the honest row is the Mathlib one you skipped, and the local file is now the thing to
retire against it — file that under `audit-authored-definitions` rather than blessing it here. A
route that points at unmapped local code is a mapping failure, not a shortcut.

#### A bundled row is matched clause by clause, and `unmatched` is the last resort

Authorship is cleared only for a unit whose mapping is `unmatched`, so `unmatched` is the most
consequential label in this repository and it is the one most easily reached by accident. A row
is `unmatched` when *every known source has been exhausted* — pinned Mathlib, current upstream,
open PRs, Reservoir, every discoverable Lean repository, and the formalization atlas — not when
the first search returned nothing convenient.

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

Before writing a new definition, derive its data, laws, hypotheses, and quantified
conditions from the source independently of the prospective Lean encoding. Ground this
in the catalogue's source unit and its mapping record; do not create a second local
account of the source.

After implementation, compare the actual declaration with that derivation. Run the
[wrong-model test](#apply-the-wrong-model-test) and the
[positive and separating examples](#require-one-positive-and-one-separating-example)
before adding the definition to `LeanCategories.All` or using it in another named
construction. Inspect mixed boundary cases, not only conditions within each part of
a partition. The examples supplement the full clause comparison and intrinsic proofs;
they do not establish equivalence by themselves.

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

Complete construction laws in Sweep III: existence where required, representative
independence, closure, category/functor laws, and the properties needed for the output
to inhabit its claimed mathematical class. An arbitrary output is not a normal-form
construction until the required normal-form property is established. A source-defined
predicate expressing that property is a different, legitimate obligation.

General classification and other theorems may remain in Sweep IV when the definition
does not depend on them. If a source theorem is required to construct or use the named
object, record its exact source-unit dependency and discharge that prerequisite.
Neither deferral of intrinsic laws nor expansion into an unrelated theorem programme
satisfies the definition sweep.

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
hypotheses/data, and source-unit dependencies. Mapping closure requires an inspected
route and supporting comparison or a scoped, dated negative search for every unit;
an admissible `unmatched` mapping does not require a Lean implementation in Sweep II.
Definition closure requires usable realizations of all definitional content. Theorem
closure requires the remaining source results with their original hypotheses and
conclusions proved. Do not apply a later phase's acceptance burden to an earlier one.

In Sweep III, direct Mathlib/project routes need the accepted semantic match and
required reachability. Package routes need the actual accepted dependency. Reference
ports need the integrated implementation and comparison, not a downloaded file or a
citation. New mathematics needs its source-grounded definition and intrinsic laws.
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

### Unfold compressed mathematical insight

An advisor can express a large structure through one short question. Treat the question as mathematical evidence, not patch instructions.

For example, ideals are submodules of the regular module. An integral basis is a basis of a specified integral algebra.

Together, these facts point toward scalar-extension functors for algebras and modules. They do not request another basis-returning method.

This general structure can remove many apparent tasks. The missing functor is mathematical compression, not expensive support work.

Removing a Sage wrapper increases the need to own the represented mathematical object. It does not remove that object.

The agent must derive the wider consequences. The advisor must not have to list every prerequisite or downstream construction.

The derivation can disagree with the advisor. Such disagreement must follow from the mathematics, not implementation convenience.

### Balance autonomous and interactive work

This repository is a research collaboration. It is not a programming queue that ends when tests pass.

The mathematician supplies ideas and intended mathematics. The agent develops the formalization and resolves routine implementation problems autonomously.

Resolve syntax errors, imports, file connections, and other representation problems without interrupting work. These changes must preserve the mathematical obligation.

Stop and discuss any problem that can change the mathematical content or research direction.

Such problems can concern truth, hypotheses, proof burden, generality, categorical placement, or conflicts between definitions. Mathlib can also misrepresent specialized mathematics.

The mathematician can also be wrong. Present the evidence and discuss the statement. Do not silently replace the intended mathematics.

This project creates new mathematics around one mathematician's programme. Existing formalizations and short proofs do not determine the intended result.

The shortest path can destroy the new theory by binding it to existing ideas too early. Sometimes the correct theory must recover those ideas.

You cannot infer the author's multi-year scope from one request. Therefore, do not decide such tradeoffs alone.

For example, an exact-sequence definition can be intended to generalize later to cofiber sequences. An equivalent classical characterization can erase that path.

Use autonomy to solve formal representation problems. Request mathematical judgment when progress requires a choice between different mathematical obligations.

Tests confirm formal consistency after that choice. They do not select the correct statement, definition, category, or research path.

Stop when you find a genuine theoretical blocker. This includes a false statement, a missing theorem, or an unresolved categorical home.

Discuss the blocker with a mathematician. Determine the acceptable compromise or alternative path together. This decision requires interactive mathematical judgment.

Do not silently change categories, definitions, objects, or statements. Do not replace a requested theorem with an easier theorem. Such substitutions are negative progress.

A silent substitution hides the failure and changes the meaning of later work. The user discovers the change only after more work depends on it.

The cost then grows. One must find the deviation, reconstruct the intent, resolve the original theory, and redo the formalization. One must also repair every dependent result.

This work is unavoidable. Pay its cost when the blocker appears. A compiling program today does not justify technical debt that can destroy the project.

Future mathematicians will learn the project from its declarations. Names and types become mathematical testimony. A misleading declaration can teach an entire dependency graph the wrong subject.

Lean certifies derivations from formal statements. It does not certify that those statements express the intended mathematics. You retain that responsibility.

The central discipline is simple but never automatic:

> Hold the mathematical object fixed. Change the representation, not the obligation.

No finite procedure guarantees this. It requires mathematical judgment, source knowledge, honest uncertainty, and willingness to leave difficult work visibly unfinished.

---

## Organize by mathematical ownership

The directory tree must express mathematical ownership.
A concept has one canonical owner.
That owner defines its category, morphisms, functors, properties, and comparison maps.

Specialized theories import general foundations.
General foundations do not import specialized subjects to recover basic definitions.
Inspect conceptual dependency direction, not only Lean's acyclic import graph.

Choose an owner from the governing universal construction.
For example, valued bilinear forms belong to formed-module theory.
Lattices then form the appropriate full subcategory.
Duals and discriminants belong where their required formed structures exist.

### Resolve parallel presentations

Two presentations can coexist only while their exact relationship is under study.
State whether that relationship is equality, equivalence, a comparison functor, or a forgetful map.

Do not import competing presentations through the root module as peer authorities.
Downstream work must use the selected canonical presentation.
After the decision, remove the superseded presentation and its downstream surface.

An equivalence does not justify a permanent parallel hierarchy.
It explains how to move existing mathematics into the canonical hierarchy.

### Make names testify accurately

Names and paths make mathematical claims.
A declaration called a functor must define an honest functor between stated categories.
A type-valued assignment plus axiomatic laws is not a functor definition.

The same rule applies to categories, morphisms, exact sequences, duals, and discriminant forms.
If the claimed structure cannot yet be defined, use a precise partial name or leave the obligation open.

Never let directory placement supply mathematical content that the declaration lacks.

### Keep the root surface coherent

The root import module is the public mathematical surface.
It must present one coherent theory, not every branch that happens to compile.

Experimental or truncated work stays outside the root surface.
State its exact relationship to the intended theory.
Promote it only after the comparison and replacement path are settled.

### Split files at mathematical boundaries

File boundaries follow standard constructions and their natural users.
They do not follow generic engineering labels or line counts.

A small end-to-end foundation can begin in one file.
Split it when distinct mathematical owners become stable.
Examples include fixed-value categories, total categories, base-change functors, duals, and cokernel constructions.

The file path should identify where a mathematician would expect the construction to live.
Moving a declaration cannot repair an incorrect mathematical owner.

### Connect catalogues through realization

A catalogue and a formalization can remain separate only with an explicit realization boundary.
Each realized catalogue entry identifies an actual Lean category, functor, predicate, or comparison.
An abstract entry remains explicitly abstract until that realization exists.

Do not let registry metadata become a second mathematical authority.
The formalized categories and functors determine the realized catalogue.

### Mathlib owns its vocabulary

The textbook catalogues list mathematical terms and source locations. They do not request
project-local synonyms for declarations that already exist in Mathlib or another dependency.

Use the canonical declaration from its owning package directly. A Mathlib term keeps its
Mathlib `Lean.Name`. An external-package term keeps that package's declaration name. Create a
`LeanCategories` name only for mathematics that this repository genuinely defines.

The CAS DSL and registry must point directly to those canonical declaration names. Never put a
project vocabulary, compatibility layer, synonym table, or translation map between the DSL and
Mathlib. Stable identifiers identify the owning Lean declarations; they do not rename them.

After the mapping acceptance boundary establishes that the existing declaration supplies the
source obligation, add nothing if it is already reachable. If it is not reachable, import its
owner. Reachability alone does not establish the match. If the mathematics is absent after
the reuse search, implement the missing object, category, functor, natural transformation,
or universal construction from a cited standard source. Do not create a wrapper whose
only purpose is to change a name.

These architectures are prohibited:

- chapter route modules consisting only of aliases to reachable declarations;
- registry entries that translate project names into Mathlib names;
- duplicate project names for package-owned mathematical objects;
- compatibility vocabularies or public-API facades over Mathlib;
- per-search notes, residue ledgers, or route cards that duplicate textbook catalogues or
  `TODO.md`.

For foundational-corpus work, search is a **corpus-wide Sweep-II deliverable**, not a private
per-consumer action. Sweep I owns mathematical source units; Sweep II owns the reproducible Lean
mapping/provenance for every unit; `TODO.md` owns active execution. Do not create extra local
route notes that compete with those two canonical records.

### Treat compilation as a structural check

A successful build proves that all imported declarations typecheck together.
It does not prove unique ownership, semantic agreement, or correct categorical placement.

Before adding a foundation to the root surface, identify its exact category and functors.
Also identify its predicates, universal properties, and relationship to existing foundations.
Apply the source comparison and separating-example check in the
[corpus acceptance workflow](#establish-the-definition-before-dependent-use) before the
root import makes that foundation available to later constructions.

---

## Reuse before you write — the operational gate

Sections 4.3–4.4 and 10.2 give the *principle* (novelty bias, false gaps, mathematical home); this is the *procedure*, and it is a hard gate. **Do not author a new definition, structure, class, or instance until you have searched for an existing one, and if you still write your own, related it to what exists.** The measure of good foundational work is accidental freedom removed (§0); the cheapest way to remove it is to not re-derive what Mathlib or a prior formalization already owns. Minimal reinvention, maximal integration-compatibility with Mathlib, is the standing default — reinvention is the failure mode, never the first move.

Before writing any **foundational-corpus** construct, in order:

1. **Require a Sweep-I source unit.** The mathematical unit must already belong to the frozen
   corpus catalogue with a stable ID, source location, kind, hypotheses/data, and dependencies.
   Do not invent scope from implementation searches or downstream demand.

2. **Require its Sweep-II mapping.** Search pinned Mathlib first, then current upstream Mathlib
   and open work, Loogle/LeanSearch/docs, Lean Reservoir, and the formalization source atlas.
   Then search GitHub broadly across all discoverable Lean repositories rather than stopping at
   the curated registry. Search names, synonyms, source theorem names, and expected type shapes.
   Open candidate code and compare mathematical generality and hypotheses.
   Apply the [mapping acceptance boundary](#accept-a-mapping-against-the-whole-source-obligation)
   to the actual declarations; a completed mapping row is not its own semantic evidence.

3. **Reuse before authorship.** A Mathlib or existing project route is used directly. An
   importable external package is imported. A non-importable Lean implementation is preserved
   with exact repository/commit/path/license provenance and ported/adapted from that reference.
   Only a unit with a completed `unmatched` mapping record is eligible for genuinely new Lean
   mathematics.

4. **Then realize the definition at its mathematical owner.** A new construct with no stated
   relationship to the standard/source notion is a red flag. Reuse Mathlib's typeclasses,
   category conventions, and morphism classes so the result composes with the library instead of
   shadowing it. Do not create project-local aliases merely to rename dependency declarations.
   Establish the source comparison and intrinsic laws before exporting the definition or
   allowing another construction to consume it.

5. **Keep search evidence in the mapping record.** The corpus catalogue owns mathematical
   source content; Sweep II owns implementation provenance. Do not create separate ad hoc route
   notes per downstream consumer. `unmatched` is a dated scoped negative search result, never a
   timeless claim that no formalization exists anywhere.

For genuinely new work outside the frozen corpus, the same reuse search applies, but first make
an explicit source/corpus-scope decision rather than silently extending corpus v1.

The failure this gate prevents is §4.3 and §4.4: writing a plausible new definition is faster and *feels* more productive than finding the three-line composition of existing constructions that already says it. That is not progress — it is a new maintenance surface and an avoidable comparison theorem later.

---

## Formalization source registry

**The highest priority of this programme is minimizing the lines of Lean owned by this repository.** Re-defining or re-proving mathematics that is already formalized anywhere online is the primary failure mode: every re-derived line is a permanent maintenance surface and an avoidable comparison theorem later. Exhaust this registry before authoring anything.

Strict preference order:

1. **Use the pinned Mathlib declaration** (`.lake/packages/mathlib`) whenever it is at least as general.
2. **Import a packaged library** as a Lake dependency (via Reservoir or a direct git dependency) when the construction lives in an active Lean 4 library.
3. **Copy or port the reference implementation** when the source is unpackaged, toolchain-incompatible, Lean 3, or in another proof assistant. Cite the origin at the ported site: repository, file, and commit or tag.
4. **Author new Lean only after 1–3 fail**, under step 3 of the reuse gate, relating the new construct to what exists in the same PR.

Every repository below resolved on GitHub on 2026-08-14. *(Lean 3)* entries are port sources only: Lean 3 code cannot enter a Lean 4 build. *(archived)* and *(stale)* flag maintenance status, not validity. Any Lean 4 repository, archived or not, is a legitimate pinned dependency exactly when it builds against this repository's toolchain and pinned Mathlib. Lake resolves one version of every package for the whole build graph from the root manifest, so a dependency compiles against this project's Mathlib — the dependency's own older Mathlib pin does not travel with it. A dormant repository often fails that test and then enters as a port with citation; when it passes, prefer the import — it is fewer owned lines. An unmaintained dependency does assign its upkeep here: the Mathlib bump that breaks it converts it to a fork-or-port at that time. Two repositories named in earlier revisions of this document no longer resolve and were removed: `BoltonBailey/FRISoundness`, and `sinhp/GroupoidModelofHoTTinLean4` (its subject now lives in [`sinhp/HoTTLean`](https://github.com/sinhp/HoTTLean)). GitHub also hosts autogenerated repository farms (for example the `*-canonical-lane-mathlib` pattern); a repository enters a plan, an import, or this registry only after a provenance check of its authors and history.

### Indexes and search surfaces

| Surface | Use |
| --- | --- |
| [Lean Reservoir](https://reservoir.lean-lang.org/) | Index of public Lake packages. Search before any general GitHub search. |
| [Loogle](https://loogle.lean-lang.org/) ([`nomeata/loogle`](https://github.com/nomeata/loogle)) | Type-pattern search over Mathlib; also the `lean_loogle` MCP tool. |
| [LeanSearch](https://leansearch.net/) | Natural-language search over Mathlib; also the `lean_leansearch` MCP tool. |
| [Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/) | Declaration-level documentation for current Mathlib. |
| [100 theorems](https://leanprover-community.github.io/100.html), [1000+ theorems](https://leanprover-community.github.io/1000.html) ([`1000-plus/1000-plus.github.io`](https://github.com/1000-plus/1000-plus.github.io)) | Which named theorems already have a formalization, in which system, and where. |
| [Undergrad math in Mathlib](https://leanprover-community.github.io/undergrad.html) | Coverage map of standard undergraduate material. |
| [Lean community projects page](https://leanprover-community.github.io/lean_projects.html) | Curated list of active formalization projects. |
| [Lean Zulip](https://leanprover.zulipchat.com/) | Search it before concluding nonexistence; in-progress formalizations are announced and discussed there. |
| [`CBirkbeck/LeanBridge`](https://github.com/CBirkbeck/LeanBridge) | Links LMFDB objects to Lean declarations. |

### Mathlib subtrees closest to this programme

The pinned checkout owns these; search them by path before any external source.

| Path | Content |
| --- | --- |
| `Mathlib/CategoryTheory/` | 1-categories, limits, adjunctions, monads, comma and elements constructions, abelian categories, monoidal and enriched categories, bicategories, sites, sheaves, topoi, localization, triangulated categories. |
| `Mathlib/AlgebraicTopology/` | Simplicial sets, nerves, quasicategories, simplicial homotopy theory. |
| `Mathlib/Condensed/` | Condensed sets and condensed abelian groups. |
| `Mathlib/AlgebraicGeometry/` | Schemes, morphism classes, gluing, Spec and Proj. |
| `Mathlib/LinearAlgebra/QuadraticForm/`, `Mathlib/LinearAlgebra/BilinearForm/` | Quadratic and bilinear forms, isometries, orthogonality. |
| `Mathlib/LinearAlgebra/RootSystem/` | Root pairings, root systems, Weyl groups. |
| `Mathlib/NumberTheory/`, `Mathlib/RepresentationTheory/` | Number fields, modular forms, L-series, group representations. |

### Category theory, higher structures, type-theory semantics

| Repository | Content |
| --- | --- |
| [`emilyriehl/infinity-cosmos`](https://github.com/emilyriehl/infinity-cosmos) | ∞-cosmos theory over Mathlib's quasicategories; formal ∞-category theory. |
| [`sinhp/HoTTLean`](https://github.com/sinhp/HoTTLean) | Groupoid and natural models of HoTT; semantics of type theory. `Groupoids/ClovenIsofibration.lean` holds a complete split-classifier story for groupoids: cloven isofibrations, fiber reindexing, `Γ ⥤ Grpd`, Grothendieck reconstruction. |
| [`sinhp/Poly`](https://github.com/sinhp/Poly) | Polynomial functors and locally cartesian closed categories. |
| [`sinhp/LeanFibredCategories`](https://github.com/sinhp/LeanFibredCategories) | Fibred categories *(stale; superseded by Mathlib's `FiberedCategory` tree and `displayed_categories`)*. |
| [`sinhp/displayed_categories`](https://github.com/sinhp/displayed_categories) | Displayed categories — the algebraic presentation of structure over a base; iso-level fibers (`EFiber`), cartesian lifts, Street fibrations *(stale; no LICENSE file — reference only, do not copy)*. |
| [`kim-em/lean-category-theory`](https://github.com/kim-em/lean-category-theory) | Early category-theory experiments, upstreamed into Mathlib *(archived)*. |
| [`rzrn/ground_zero`](https://github.com/rzrn/ground_zero) | HoTT library in Lean 4 *(archived)*. |
| [`gebner/hott3`](https://github.com/gebner/hott3) | HoTT *(Lean 3)*. |

### Algebra, number theory, algebraic geometry

| Repository | Content |
| --- | --- |
| [`ImperialCollegeLondon/FLT`](https://github.com/ImperialCollegeLondon/FLT) | Ongoing Fermat's Last Theorem formalization; substantial reusable commutative algebra, dimension theory, and number theory beyond the headline target. Its `FLT/Mathlib/` staging tree holds small upstream-bound files (integral adeles, tensor-versus-restricted-product equivalences); toolchain and Mathlib pin run ahead of this repo, so port those files rather than depend. Contains no quadratic-form or lattice theory. |
| [`leanprover-community/flt-regular`](https://github.com/leanprover-community/flt-regular) | FLT for regular primes; cyclotomic-field material. |
| [`kbuzzard/ClassFieldTheory`](https://github.com/kbuzzard/ClassFieldTheory) | 2025 Clay Summer School project on class field theory. Consumes Mathlib's local-field classes rather than building completion infrastructure; no higher unit groups. |
| [`mariainesdff/LocalClassFieldTheory`](https://github.com/mariainesdff/LocalClassFieldTheory) | Local fields, toward local class field theory. Best external DVR/uniformizer API for completions at height-one primes, but *(no LICENSE file — proof-strategy reference only)*, stale toolchain, and a `sorry` inside its `isDiscrete` instance. |
| [`AntoineChambert-Loir/DividedPowers4`](https://github.com/AntoineChambert-Loir/DividedPowers4) | Divided power structures and the divided-power algebra. The core construction is upstreamed in Mathlib `RingTheory/DividedPowerAlgebra/Init`; the grading and polynomial-law layers are not. No LICENSE file and a partially built source tree: reference only, do not copy code from it. |
| [`YaelDillies/toric`](https://github.com/YaelDillies/toric) | Toric varieties over Mathlib's schemes. |
| [`MichaelStollBayreuth/EulerProducts`](https://github.com/MichaelStollBayreuth/EulerProducts) | Euler products and L-series. |
| [`MichaelStollBayreuth/Heights`](https://github.com/MichaelStollBayreuth/Heights) | Theory of heights. |
| [`CBirkbeck/AINTLIB`](https://github.com/CBirkbeck/AINTLIB) | Atlas of formalized number theory. |
| [`ANR-FALSE/PadicModForms`](https://github.com/ANR-FALSE/PadicModForms) | p-adic modular forms. |
| [`loefflerd/ModularFormDimensions`](https://github.com/loefflerd/ModularFormDimensions) | Finite-dimensionality of modular-form spaces. |
| [`CBirkbeck/ModularForms_Lean4`](https://github.com/CBirkbeck/ModularForms_Lean4) | Modular forms, largely upstreamed into Mathlib *(stale)*. |
| [`CBirkbeck/DirichletNonvanishing`](https://github.com/CBirkbeck/DirichletNonvanishing) | Nonvanishing of Dirichlet L-functions *(archived)*. |
| [`CBirkbeck/WeilConverse`](https://github.com/CBirkbeck/WeilConverse) | Weil converse theorem. |
| [`AlexKontorovich/PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | Prime Number Theorem and related analytic number theory. |
| [`math-inc/strongpnt`](https://github.com/math-inc/strongpnt) | Strong PNT with complex-analysis infrastructure; AI-generated, human-reviewed. |
| [`teorth/expdb`](https://github.com/teorth/expdb) | Exponent-pair database for analytic number theory. |
| [`b-mehta/ABC-Exceptions`](https://github.com/b-mehta/ABC-Exceptions) | Exceptions to the ABC conjecture. |

### Quadratic forms, lattices, sphere packing

| Repository | Content |
| --- | --- |
| [`thefundamentaltheor3m/Sphere-Packing-Lean`](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean) | Viazovska's dimension-8 sphere packing; E8 lattice. Already integrated here under `Integration/SpherePacking` and `LeanCategoriesSpherePacking/E8`. |
| [`mariainesdff/HassePrinciple`](https://github.com/mariainesdff/HassePrinciple) | Hilbert symbols and the Hasse–Minkowski invariant over general fields (Women in Numbers 7). Definitions in place; the key choice-independence proofs are still `sorry`. Apache 2.0, but the team accepts no outside contributions — copy with attribution. |
| [`roed-math/gq2-lean`](https://github.com/roed-math/gq2-lean) | Dyadic Hilbert symbol over ℚ₂ with Serre's evaluation formula and 2-adic square-class facts, sorry-free and self-contained inside a profinite `G_{ℚ₂}` presentation. Apache 2.0. |
| [`MichaelStollBayreuth/LegendreQF`](https://github.com/MichaelStollBayreuth/LegendreQF) | Legendre's theorem on diagonal ternary quadratic forms; complete but defines no Hilbert symbol, Hasse invariant, or lattice notion. |
| [`jonhanke/quadratic_forms_in_lean`](https://github.com/jonhanke/quadratic_forms_in_lean) | Skeleton only: the library files carry reference comments (Cassels) and a few thin definitions, no theorems; no LICENSE file. Do not mine. |

### Analysis, probability, geometry, dynamics

| Repository | Content |
| --- | --- |
| [`teorth/analysis`](https://github.com/teorth/analysis) | Lean companion to Tao's *Analysis I*. |
| [`fpvandoorn/carleson`](https://github.com/fpvandoorn/carleson) | Carleson's theorem. |
| [`fpvandoorn/BonnAnalysis`](https://github.com/fpvandoorn/BonnAnalysis) | Bonn collaborative analysis seminar (distributions, duality). |
| [`leanprover-community/sphere-eversion`](https://github.com/leanprover-community/sphere-eversion) | Sphere eversion via convex integration; h-principle. |
| [`RemyDegenne/brownian-motion`](https://github.com/RemyDegenne/brownian-motion) | Construction of Brownian motion. |
| [`RemyDegenne/testing-lower-bounds`](https://github.com/RemyDegenne/testing-lower-bounds) | Information theory and hypothesis-testing bounds. |
| [`oliver-butterley/SpectralThm`](https://github.com/oliver-butterley/SpectralThm) | Spectral theorem. |
| [`girving/ray`](https://github.com/girving/ray) | Mandelbrot-set results. |
| [`girving/interval`](https://github.com/girving/interval) | Verified floating-point interval arithmetic. |
| [`leanprover-community/lean-liquid`](https://github.com/leanprover-community/lean-liquid) | Liquid Tensor Experiment *(Lean 3; condensed foundations now in Mathlib)*. |
| [`leanprover-community/lean-perfectoid-spaces`](https://github.com/leanprover-community/lean-perfectoid-spaces) | Perfectoid spaces *(Lean 3)*. |
| [`dagurtomas/lean-solid`](https://github.com/dagurtomas/lean-solid) | Solid abelian groups *(stale)*. |
| [`ImperialCollegeLondon/condensed-sets`](https://github.com/ImperialCollegeLondon/condensed-sets) | Early condensed mathematics *(Lean 3)*. |

### Combinatorics, discrete mathematics, logic, foundations

| Repository | Content |
| --- | --- |
| [`teorth/equational_theories`](https://github.com/teorth/equational_theories) | Implication graph between magma equational laws. |
| [`teorth/pfr`](https://github.com/teorth/pfr) | Polynomial Freiman–Ruzsa conjecture and related additive combinatorics. |
| [`YaelDillies/cam-combi`](https://github.com/YaelDillies/cam-combi) (formerly `LeanCamCombi`) | Cambridge graph theory and combinatorics courses. |
| [`YaelDillies/apap`](https://github.com/YaelDillies/apap) (formerly `LeanAPAP`) | Kelley–Meka bound on Roth numbers. |
| [`apnelson1/Matroid`](https://github.com/apnelson1/Matroid) | Matroid theory over Mathlib. |
| [`Ivan-Sergeyev/seymour`](https://github.com/Ivan-Sergeyev/seymour) | Seymour's decomposition theorem for regular matroids. |
| [`madvorak/vcsp`](https://github.com/madvorak/vcsp) | General-valued constraint satisfaction. |
| [`madvorak/duality`](https://github.com/madvorak/duality) | Linear-programming duality. |
| [`siddhartha-gadgil/Polylean`](https://github.com/siddhartha-gadgil/Polylean) | Group extensions and torsion-freeness with computational proofs. |
| [`leanprover-community/con-nf`](https://github.com/leanprover-community/con-nf) | Consistency of Quine's New Foundations. |
| [`flypitch/flypitch`](https://github.com/flypitch/flypitch) | Independence of the continuum hypothesis *(Lean 3)*. |
| [`FormalizedFormalLogic/Foundation`](https://github.com/FormalizedFormalLogic/Foundation) | Mathematical logic: completeness, incompleteness, provability logic. |
| [`avigad/lamr`](https://github.com/avigad/lamr) | *Logic and Mechanized Reasoning* textbook and code. |

### Computational and applied mathematics

| Repository | Content |
| --- | --- |
| [`lecopivo/SciLean`](https://github.com/lecopivo/SciLean) | Scientific computing. |
| [`leanprover-community/physlib`](https://github.com/leanprover-community/physlib) (formerly PhysLean/HepLean) | Physics results in Lean. |
| [`Timeroot/Lean-QuantumInfo`](https://github.com/Timeroot/Lean-QuantumInfo) | Quantum information theory. |
| [`optsuite/optlib`](https://github.com/optsuite/optlib) | Optimization algorithms and convergence proofs. |
| [`verified-optimization/CvxLean`](https://github.com/verified-optimization/CvxLean) | Convex optimization modeling *(stale)*. |
| [`ufmg-smite/lean-smt`](https://github.com/ufmg-smite/lean-smt) | SMT-solver tactics. |
| [`eric-wieser/lean-matrix-cookbook`](https://github.com/eric-wieser/lean-matrix-cookbook) | The Matrix Cookbook, proved. |
| [`leanprover/cslib`](https://github.com/leanprover/cslib) | Computer science library. |
| [`leanprover-community/iris-lean`](https://github.com/leanprover-community/iris-lean) | Iris separation logic port. |
| [`or4nge19/NeuralNetworks`](https://github.com/or4nge19/NeuralNetworks) | Neural networks. |
| [`shetzl/autth`](https://github.com/shetzl/autth) | Automata theory. |

### Statement banks and generated corpora — always search these

| Repository | Content |
| --- | --- |
| [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures) | Formalized conjecture statements. When it has a relevant one, import, reuse, or extend it — never restate it from scratch. Sanctioned home for genuinely-unproved deep statements (conjecture ledger, issue #21). |
| [`facebookresearch/atlas-lean`](https://github.com/facebookresearch/atlas-lean) | ATLAS Autoformalized Textbook Library At Scale. Search for textbook definitions, statements, and dependency chains before reconstructing standard mathematics from prose. |
| [`facebookresearch/algebraic-combinatorics`](https://github.com/facebookresearch/algebraic-combinatorics) | Automatic formalization of Grinberg's *Algebraic Combinatorics*. |
| [`facebookresearch/autoform-bot`](https://github.com/facebookresearch/autoform-bot), [`facebookresearch/repoprover`](https://github.com/facebookresearch/repoprover) | ATLAS formalization pipeline and textbook-formalization research code; use to locate generated corpora and source projects. |
| [`facebookresearch/LeanUniverse`](https://github.com/facebookresearch/LeanUniverse) | Index and manager of Lean libraries and datasets. |
| [`facebookresearch/abel`](https://github.com/facebookresearch/abel), [`facebookresearch/Evariste`](https://github.com/facebookresearch/Evariste) | Proof-search systems and their corpora. |
| [`dwrensha/compfiles`](https://github.com/dwrensha/compfiles) | Catalog of formalized competition problems. |
| [`ShouqiaoW/erdos`](https://github.com/ShouqiaoW/erdos) | Erdős problems: checked proofs, partially formalized in Lean. |
| [`trishullab/PutnamBench`](https://github.com/trishullab/PutnamBench) | Putnam problems in Lean 4, Isabelle, and Coq. |
| [`google-deepmind/alphaproof-nexus-results`](https://github.com/google-deepmind/alphaproof-nexus-results) | AlphaProof-generated Lean proofs with prose companions. |
| [`TauCetiProject/TauCeti`](https://github.com/TauCetiProject/TauCeti) | AI-implemented, human-directed library downstream of Mathlib. |
| [`mo271/FormalBook`](https://github.com/mo271/FormalBook) | Aigner–Ziegler, *Proofs from THE BOOK*. |

### Textbook companions and worked proof corpora

| Repository | Content |
| --- | --- |
| [`leanprover-community/mathematics_in_lean`](https://github.com/leanprover-community/mathematics_in_lean) | *Mathematics in Lean* tutorial. |
| [`hrmacbeth/math2001`](https://github.com/hrmacbeth/math2001) | Proof-writing course, paper and Lean. |
| [`djvelleman/HTPILeanPackage`](https://github.com/djvelleman/HTPILeanPackage) | *How To Prove It* companion. |
| [`PatrickMassot/GlimpseOfLean`](https://github.com/PatrickMassot/GlimpseOfLean) | Fast introduction to theorem proving. |
| [`leanprover-community/NNG4`](https://github.com/leanprover-community/NNG4) | Natural Number Game. |

### Core libraries and infrastructure

| Repository | Content |
| --- | --- |
| [`leanprover-community/batteries`](https://github.com/leanprover-community/batteries) | Extended standard library. |
| [`leanprover-community/aesop`](https://github.com/leanprover-community/aesop) | White-box proof automation. |
| [`leanprover-community/duper`](https://github.com/leanprover-community/duper), [`leanprover-community/lean-auto`](https://github.com/leanprover-community/lean-auto) | Automated theorem proving in Lean. |
| [`leanprover-community/plausible`](https://github.com/leanprover-community/plausible) | Property-based counterexample search. |
| [`leanprover-community/repl`](https://github.com/leanprover-community/repl) | Programmatic proof checking. |
| [`PatrickMassot/leanblueprint`](https://github.com/PatrickMassot/leanblueprint) | Formalization blueprint infrastructure. |
| [`siddhartha-gadgil/LeanAide`](https://github.com/siddhartha-gadgil/LeanAide) | AI aids for autoformalization. |

### Other proof assistants — porting sources only

| Repository | Content |
| --- | --- |
| [`UniMath/UniMath`](https://github.com/UniMath/UniMath) | Univalent mathematics in Rocq/Coq; large formal category-theory corpus. |
| [`HoTT/Coq-HoTT`](https://github.com/HoTT/Coq-HoTT) | Homotopy type theory in Rocq/Coq. |
| [`math-comp/math-comp`](https://github.com/math-comp/math-comp), [`math-comp/odd-order`](https://github.com/math-comp/odd-order) | Mathematical Components; the Odd Order Theorem. |
| [`rocq-community/corn`](https://github.com/rocq-community/corn) | Constructive mathematics repository at Nijmegen. |
| [`UniMath/agda-unimath`](https://github.com/UniMath/agda-unimath) | Univalent mathematics in Agda, including extensive category theory. |
| [`agda/cubical`](https://github.com/agda/cubical) | Cubical Agda library. |
| [`the1lab/1lab`](https://github.com/the1lab/1lab) | Cross-linked HoTT reference in cubical Agda. |
| [`martinescardo/TypeTopology`](https://github.com/martinescardo/TypeTopology) | Topology and logic from the univalent point of view, in Agda. |
| [Isabelle Archive of Formal Proofs](https://www.isa-afp.org/) | Searchable archive of Isabelle developments by topic. |

---

## Sourcing a citation — the source gate

The reuse gate above governs *formalizations*; this one governs *mathematical sources*. Much of this programme's content is transcribed from the literature — Nikulin's genus theorems, O'Meara's modularity, Conway–Sloane, Kac. **A citation entering a plan, issue, docstring, or commit message carries an item key from the live library and a statement read on the page.**

Before citing any paper, book, or theorem number, in order:

1. **Load the [[zotero/SKILL|zotero]] skill and read through the live library.** It owns the transport: the running Zotero desktop's local API, `lib/zotero.py` in the `zotero-library` repo, `health()` first. Follow it rather than a remembered command surface. The library is what supplies the item key that makes a citation resolvable by a later agent.

2. **Use [[zotero-metadata-proof/SKILL|zotero-metadata-proof]] and [[zotero-pdf-extraction-attachments/SKILL|zotero-pdf-extraction-attachments]]** when the question is whether an item's metadata is right, or whether the text in hand is the item's current extraction child. `get_children` paginates, so confirm the full child list before concluding what attachments an item has.

3. **Transcribe the numbered result, and label its role.** Quote the statement as the source gives it, and say whether it is a *definition* or a *characterization*. The distinction carries the hypotheses and names the auxiliary invariants the definition depends on — which is how a missing ingredient becomes visible (§3.5: implications are theorems, not definitions).

4. **Report searches in the reuse gate's form** — name the scope searched (§10.7).

### Read the Zotero extraction corpus

Search the local Zotero Markdown extractions before searching the web or relying on memory.
The extraction corpus is live under `~/Zotero/storage`; it is not a repository mirror.

```bash
cd /home/dzack/zotero-library
just search 'period domain' -- -C2
just search 'Nikulin' -- -w
```

`just search` performs a case-insensitive regular-expression search over
`*_extracted.md` files. It prints matching lines, the parent Zotero key, and a
`zotero://select` link. Treat this output as a locator. Read the matching Markdown
attachment itself and record the relevant line numbers or page markers. A search miss
means only that the inspected extraction corpus had no match.

### Use the local PDF when the extraction is unclear

The Markdown child is the searchable transcription. When a formula, symbol, page
layout, or OCR passage is unclear, open the PDF child attached to the same parent and
inspect the cited page locally. Resolve its file path from the attachment record's
`links.enclosure` field. This preserves the source identity already established in
Zotero.

Use the local PDF to confirm notation, page numbers, and theorem statements. If the
local PDF needs a new text extraction, route it through [[reading-pdfs/SKILL|reading-pdfs]]
and the managed Zotero extraction workflow. A publisher or web copy is relevant when
the source identity or edition remains unresolved; it is not a presumed improvement to
the local extraction.

When local inspection confirms material OCR defects, add the `bad-ocr` tag to the parent
bibliographic item with `add_item_tags(parent_key, ["bad-ocr"])`. Tag the parent rather
than its PDF or Markdown child so later triage sees the source item.

Resolve the source identity through live Zotero before citing it. Call `health()` first,
then use `get_data(parent_key)` for the parent and paginated `get_children(parent_key)`
to find the child whose `data.contentType` is `text/markdown` and whose filename ends in
`_extracted.md`. Read that file at
`~/Zotero/storage/<attachment-key>/<filename>`. If the desktop or local addon is down,
report that blocker; do not use the cloud API or a translation-server fallback.

The parent item's `data.citationKey` is the Better BibTeX key. Use that exact key in the
target document's citation syntax: `[@key]` in Pandoc Markdown or `\cite{key}` in
LaTeX. Add a locator when the extraction supplies one, for example `[@key, p. 12]`.
Never invent a key, derive one from the author or year, or cite only the Zotero key.
When reporting a source, include its Zotero key, Better BibTeX key, creator, and title.

What this gate buys: a citation that resolves, a statement checked against the page, and the auxiliary notions the source's own definition requires. The third is the one that pays — a definition transcribed from the page brings its ingredients with it, and those ingredients are how the catalogue learns which invariants it still owes.

---

## 1. What the project is actually building

### 1.1 Not a category taxonomy

The long-term ambient is at least an **$(\infty,2)$-categorical universe of $\infty$-categories**: objects are $\infty$-categories, 1-morphisms are functors, and 2-morphisms include the natural transformations needed by the programme. This is not a demand that every first implementation formalize all higher-category theory. It is the semantic target against which ordinary Mathlib `Cat`, strict categories, and early computational spikes are understood as truncated realizations. That distinction prevents a successful early model from becoming an accidental ceiling.

The intended object is not a tree of names and not a normalized version of Sage’s class hierarchy. It is a mathematical presentation containing categories, functors, higher cells, parameterized families, categories of structured objects, limits, and named equivalences. A parent graph is only a view of this richer object.

A taxonomy answers “what label is above what label?” The project needs to answer stronger questions:

- What is the category being named?
- What are its objects and morphisms?
- Which functor forgets or compares its structure?
- Which diagrams commute, strictly or coherently?
- Which constructions are primitive and which are induced?
- Under what domain is an invariant functorial?
- Which choices are contractible and which must be named?
- How does a computational method arrive by functorial composition?

The attached conversations repeatedly move from labels to this calculus. “A category is abelian,” for example, is replaced by a point of the category of categories together with a lift through the classifier of abelian categories. The assertion becomes a factorization with a witness, hence something composable and auditable rather than prose. [S1]

### 1.2 Not a Sage rewrite

Sage is simultaneously valuable and non-authoritative:

- it contains a large inventory of mathematical domains;
- it contains algorithms and dispatch knowledge;
- it records an empirical parent graph;
- it exposes historical approximations and naming defects.

The bridge is not meant to reproduce that graph faithfully as mathematics. It is meant to state what Sage’s categories and constructions correspond to in a normalized universe, and to retain Sage as an implementation where useful. The mathematical definitions determine the bridge, not the other way around.

### 1.3 Not a Lean-flavoured programming language

Lean is the formalization substrate. It provides definitions, theorem statements, proofs, and a trust boundary for the foundational library and verified certificates. The DSL is a computational language for mathematicians. Its user does not reason in Lean implementation vocabulary, choose typeclass instances, select a backend representation, or manually traverse an implementation graph.

The intended user experience is categorical membership:

```text
let R ∈ CRings
let M ∈ Modules(R)
let F ∈ Fun(CRings, Sets)
compute F(R)
```

and, for concrete objects,

```text
let R := ZZ ∈ Rings
let I := (2) ∈ Ideals(R)
let Q := R / I
Q.cardinality()
Q.generators()
```

The system may internally elaborate, infer routes, invoke Sage, use Mathlib, choose a matrix algorithm, or check a certificate. None of those mechanisms changes what `R`, `I`, or `Q` mathematically are. The DSL discussion repeatedly insists that the user states membership, that the categorical context determines the available operations, and that the user does not select the algorithm manually. [S4]

### 1.4 Not a proof-completion programme for every difficult theorem

The foundational work supplies the language in which downstream results can be stated and computations can be performed. It does not improve the foundation by pulling major classification, termination, Torelli, MMP, gluing, or compactification theorems into the first layer merely because those topics occur later in the research programme.

The long-term programme is broad in **definitions and categorical homes**. It is deliberately selective in **hard theorem burden**. Confusing breadth of language with breadth of theorem formalization is one of the ways agents overscope the foundation while still missing its true generality.

---

## 2. Why the higher-categorical foundation is a simplification

### 2.1 It replaces many ad hoc mechanisms by one recursive construction

A stable theme of the conversations is that the same pattern recurs at successive categorical levels.

- A set with a binary operation is a point of `Set` lifted through an operation classifier.
- A module with a form is a point of a module category lifted through a form classifier.
- A category with a monoidal or abelian structure is a point of the category of categories lifted through the corresponding classifier.

The ambient changes; the construction does not. The source discussions summarize this as one classifier-and-lift primitive over a variable ambient, with structure on an object and structure on a category as the same move at adjacent levels. [S5]

This is precisely the kind of abstraction that decreases work. It eliminates separate “systems” for set-level axioms, module-level enhancements, category-level structures, and later higher-categorical coherence.

### 2.2 It gives comparisons a home

Many relationships needed by the programme are not additional functors between additional objects. They are natural transformations, modifications, equivalences, or coherences between composites.

When an agent insists on a 1-dimensional graph, these relationships are forced into one of several corrupt forms:

- fake nodes representing values such as `O(L)`;
- duplicate direct arrows representing composites;
- route strings and path-length rules;
- “preferred” edges without a mathematical universal property;
- prose assertions that two constructions agree;
- extra wrapper categories created only to hold comparison data.

At the correct categorical level, the comparison is simply a 2-cell. The conversations use the example of applying the generic automorphism construction to a projection or discriminant functor: the resulting maps are components of a natural comparison, not manually declared special edges. [S1]

### 2.3 It makes coherence native rather than exceptional

A binary operation can be constructed uniformly by an arrow-category pullback. An equation or coherent axiom is represented by a boundary diagram built from the universal operation and a space or category of fillers. Associativity and commutativity are the low-dimensional grounding cases; pentagons and operadic matching diagrams are not separate mechanisms but higher instances of the same pattern. [S3]

This is the long-term importance of the higher ambient. A framework that only encodes strict equality between two composites may be enough for the first magma example but will require replacement when monoidal categories, higher algebra, stacks, or genuine synthetic infinity-category theory arrive. The general diagram-and-filler construction is not scope inflation; it is the shared definition that prevents repeated redesign.

### 2.4 It deletes degrees of freedom

The conversations explicitly identify mathematical simplicity with deletion of choices:

- a prose assertion admits unbounded paraphrases;
- a factorization has a fixed universal meaning;
- a pointwise construction admits one special case per object;
- a functor gives all cases at once;
- a manually maintained hierarchy admits arbitrary omitted edges;
- a generated presentation derives all composites;
- an unnamed structure can silently change;
- a named section fixes which point of a noncontractible fiber is used.

The target is not “maximum generality” in the abstract. It is the **lowest generating level in the correct higher ambient**. Overcategorifying a genuinely set-level invariant is also drift. Truncation level is mathematical content, and the source discussions use the genus example to show that promoting a set-level fiber to a homotopy pullback changes the object rather than generalizing it. [S2]

---

## 3. The stable mathematical style being taught

This section records the style of thought repeatedly demanded in the conversations. It is more fundamental than any particular issue plan.

### 3.1 Propositions become morphisms one level up

An assertion about an object is replaced by a map into a classifying object, and the assertion becomes a lift or factorization. This turns inert prose into categorical data subject to composition, pullback, whiskering, and coherence.

This is not a coding trick. It is the same mathematical move seen in classifying maps, reduction of structure group, moduli problems, and obstruction theory. The source calls it the master principle behind the simplifications. [S1]

### 3.2 Declare generic assignments, not their values

`O(L)`, `GL(M)`, a unit group, a fundamental group, and a Galois group are usually values of generic constructions. A value is not promoted to a category node or primitive declaration merely because it is important in one example.

The repeated `O(L)` failures are diagnostic. Once the generic automorphism functor is present, orthogonal groups, automorphism groups of discriminant forms, and induced homomorphisms arise by evaluation and functoriality. Special treatment of the instance increases ontology size while hiding its relationship to the generic construction.

### 3.3 One primitive per parameterized family

Right modules, a particular rank, a particular lattice, or a particular coefficient module are values or fibers of parameterized families unless mathematics supplies a genuinely different construction. A special case does not become primitive because it is the first case used by a worked example.

This is the same objection to rank-two wrappers, object-specific orthogonal-group nodes, and one category per chosen monoidal structure. The parameter or section belongs to the value or lift, not to a proliferating family of classifier nodes.

### 3.4 Own an axiom where the constrained operation first exists

Commutativity belongs where a binary operation exists, not separately at rings, groups, semirings, and algebras. The higher categories are obtained by pulling the classifier back along structural functors.

The point is not merely code reuse. It is semantic correctness: a condition transports exactly when it factors through the relevant functor. Finite generation of a group does not become finite generation of the underlying monoid; the failure of factorization is the mathematical reason no transport exists.

### 3.5 Implications are theorems, not definitions

Alternating and skew-symmetric forms can be defined independently at their natural owner. The implication from one to the other is a theorem with a witness. Nesting one definition inside the other may make a tree look minimal, but it encodes a theorem as ontology and loses the direct relationship to the general ambient definition.

The same warning applies whenever an agent restructures definitions merely to make an implication, comparison, or special-case theorem “automatic.” A theorem becoming definitional is not automatically a simplification.

### 3.6 Present generators and relations; do not enumerate composites

The diagram contains adjacent structural functors and the necessary coherence relations. Distant forgetful maps are composites. Induced projections arise from limits. Whiskered comparisons arise from higher functoriality.

This is the categorical analogue of a presentation rather than a multiplication table. It both reduces the declaration surface and makes coherence visible where it belongs: as a relation between paths.

### 3.7 Property, structure, and stuff are properties of fibers

The project uses one classifier formalism. The difference between property, structure, and stuff is read from the classifying fibers and their truncation, not stored as an independent taxonomy. Properties are the propositional end of a nested filtration, not a disjoint species.

This matters operationally. If the fiber is contractible when inhabited, a consumer need not name a choice. If the fiber has multiple points or higher morphisms, the consumer must name the chosen section. The source uses multiple monoidal structures on the same category as the grounding example: one monoidal classifier, several named lifts. [S6]

### 3.8 Everything is up to the appropriate equivalence

Categories, higher categories, and their constructions are not identified merely because their names or endpoints match. Equivalences and coherent comparison cells are explicit mathematical data. A shortest path is not a coherence theorem. A string identifier is not an equality of functors.

This convention is what makes pseudo-pullbacks, homotopy pullbacks, and isofibration hypotheses structural rather than ornamental.

### 3.9 Truncation level is content

A set of isomorphism classes, a groupoid of objects and isomorphisms, and an infinity-groupoid are different mathematical objects. Passing to a core, taking `π₀`, or replacing a strict limit by a homotopy limit is never a harmless display choice.

The project uses higher categories to retain exactly the coherence that is mathematically present. It does not use them decoratively to replace every set-level construction by a more derived object.

### 3.10 Define through governing diagrams and exact sequences

The mathematical style extends beyond categorical placement. A map alone is often not the object. A truncated exact sequence is often not enough. The radical, cokernel, connecting morphism, discriminant object, and obstruction class are part of the definition’s natural environment.

The source extracts a “homological presentation” convention:

- name the full exact sequence or governing long exact sequence;
- name kernels, cokernels, and connecting morphisms;
- express a property as the vanishing or exact position of a named obstruction;
- state the domain on which a construction is functorial;
- present invariants as truncations or shadows of a named categorical or homological construction.

Use this convention as the default definitional framework. When the ambient category
has the required constructions, do not define predicates element by element. Prefer:

- vanishing kernels to pointwise zero conditions or injectivity;
- vanishing cokernels to quotient presentations or surjectivity;
- vanishing terms in exact sequences to bijectivity or isomorphism conditions;
- fibers and cofibers to kernel and cokernel models in homotopical settings;
- pullbacks, pushouts, limits, and colimits to elementwise compatibility conditions.

Choose definitions that still make sense in categories without elements, including
categories of sheaves. Also preserve their extension to derived, homotopical, and
infinity-categorical settings. Prove elementwise formulas and simpler recognition
criteria as consequences only when a consumer needs them.

This is why “nondegenerate means the adjoint is injective” is mathematically poorer than a named radical/discriminant sequence in which nondegeneracy and perfectness occupy identifiable positions. [S2]

### 3.11 Mathematical prose is audited by human mathematicians

The intended auditor is a working mathematician, not a software engineer, programming-language researcher, logician, or another agent trained on project coinage. Advanced category theory is admissible because it has a standard mathematical definition and literature. Unfamiliarity is not the problem. Unauditability is.

The sources distinguish three dangerous language classes:

- foreign technical vocabulary whose rigorous meaning belongs to a literature the intended reader cannot police;
- local coinage and LLM-generated nouns with no external definition;
- collisions where a standard mathematical word is repurposed for infrastructure.

The rule is one-directional: implementation vocabulary may exist inside Lean or backend code, but it does not flow upward into the mathematical language or DSL. [S7]

---

## 4. The observed anatomy of agent drift

The following are not hypothetical risks. They recur across the attached conversations and failed spikes.

### 4.1 Code-as-ontology capture

**Observed pattern.** The agent starts from an existing declaration and asks what mathematical story can justify preserving it.

**Why it drifts.** The code tree becomes the invariant; mathematics becomes post-hoc explanation. A wrapper, accessor, or category is presumed to have a right to exist because work has already been invested in it.

**Long-term damage.** A malformed early ontology becomes harder to remove after it accumulates proofs, exports, documentation, and downstream consumers. Lean can prove many theorems about the wrong object.

**Characteristic signal.** “We can keep this declaration if we prove an equivalence/tether to the standard one.”

### 4.2 Local repair bias

**Observed pattern.** A correction triggers a new field, tag, registry rule, exception, or validation pass at the site of the error.

**Why it drifts.** The correction is treated as an isolated defect rather than evidence that the ambient formalism is wrong.

**Long-term damage.** Every patch creates another concept that future agents must remember. The system grows a defect taxonomy rather than removing the expressibility of the defect.

The source summarizes the alternative question precisely: not “how do we flag this wrong node?” but “what standard theory makes this node impossible to state?” [S1]

### 4.3 Novelty and artifact bias

**Observed pattern.** A large graph, schema, manifest, or bespoke abstraction feels like more progress than citing a standard construction and deleting code.

**Why it drifts.** Model behaviour rewards visible production. “There is nothing to invent” looks insufficiently active.

**Long-term damage.** Reinvention produces a new vocabulary and maintenance surface while obscuring the fact that the mathematics was already compositional.

### 4.4 Exact-name fixation and false gaps

**Observed pattern.** If Mathlib or the literature has no declaration with exactly the desired project name, the agent concludes that the mathematics is missing.

**Why it drifts.** Standard mathematics is frequently a composition of categories of elements, comma categories, full subcategories, pullbacks, cores, sections, and equivalences.

**Long-term damage.** The project acquires duplicates of standard constructions and later must prove avoidable comparison theorems or reconcile incompatible APIs.

### 4.5 Relation-kind collapse

**Observed pattern.** Identity, definitional equality, equivalence, ingredient, chosen presentation, property, structure, implementation, and example are treated as interchangeable forms of “correspondence.”

**Examples from the failed work.**

- a bilinear form treated as the lattice;
- a chosen basis treated as finite freeness;
- an enumeration treated as finiteness or countability;
- an equivalence treated as permission to erase chosen data;
- an invariant accessor placed on every structured category that can eventually reach its domain.

**Long-term damage.** The graph ceases to state which claims are mathematical and which are presentation choices. Later algorithms consume the wrong data or silently assume noncanonical choices.

### 4.6 Proof-carrying laundering

**Observed pattern.** Once a local declaration has a verified relationship to a standard one, the relationship is treated as proof that the local declaration is legitimate.

**Why it drifts.** Internal consistency is confused with faithful modeling. A theorem that a ring-specific `size` equals underlying-set cardinality may prove that the ring-specific declaration is redundant, not that it belongs on the ring.

**Long-term damage.** Proofs strengthen the wrong ontology and make it more convincing. Green builds become evidence against rethinking definitions.

### 4.7 Capability-to-ontology promotion

**Observed pattern.** A backend requirement becomes a mathematical category or field.

Examples include enumeration-equipped categories, basis data made intrinsic, algorithm support turned into mathematical structure, or Sage dispatch categories copied into Lean.

**Why it drifts.** The agent sees the immediate implementation need but not the standard mathematical category in which the needed choice already lives.

**Long-term damage.** The mathematical universe becomes a mirror of current backend capabilities. Replacing the backend or adding another one requires changing the ontology.

The project’s intended distinction is subtler: a basis, generating family, or Gram matrix can be honest mathematical structure in a comma category or category of structured objects; an algorithm can return a point in the corresponding fiber. The error is not “chosen data exists.” The error is promoting an engineering convenience without first locating its standard mathematical home.

### 4.8 Singleton reification

**Observed pattern.** The first worked example becomes a named category or primitive abstraction: rank two, one lattice, one group, one route.

**Why it drifts.** The example is concrete and testable, whereas the family requires a parameter and a universal definition.

**Long-term damage.** Every new example adds another special surface. Generalization later becomes a rewrite instead of evaluation of an existing family.

### 4.9 Proxy optimization

**Observed pattern.** Hard mathematical judgment is replaced by counts: number of untethered declarations, number of rows with reasons, number of passing checks, number of remaining “residues.”

**Why it drifts.** The proxy is measurable and gives a visible downward trend. Difficult cases can be removed from the denominator by reclassification.

**Long-term damage.** Progress-shaped evidence accumulates while the foundational classification remains unresolved.

### 4.10 Principle–action decoupling

**Observed pattern.** The agent can state the correct principle in prose and then immediately violate it in the next edit.

The source calls this “doctrine held as material, not as lens”: the principle is something documented or enforced on other declarations, not the rule controlling the agent’s own next action.

**Long-term damage.** Verbal agreement produces false confidence. The conversation appears aligned while the implementation continues on the old invariant.

### 4.11 Correction as theorem patch rather than ontology reset

**Observed pattern.** A counterexample produces a local lemma or special exception.

**Why it drifts.** Re-deriving downstream classifications is expensive, so the agent preserves them and patches the contradiction.

**Long-term damage.** A counterexample that invalidates an entire classification scheme is contained instead of propagated. The ontology becomes a stratigraphy of past mistakes.

### 4.12 Formalization at typing speed

**Observed pattern.** As soon as a promising categorical vocabulary appears, the agent starts writing code before variance, direction, morphisms, truncation, and universal properties have been settled.

**Why it drifts.** Advanced terminology makes the construction sound principled. Code generation is faster than mathematical deliberation.

**Long-term damage.** Discretionary choices become implicit in types and are later defended as implementation facts.

The attached history contains repeated moves from one prematurely selected construction to another—inserters, equifiers, quotient language, low-dimensional squares—before the more uniform arrow-category, full-diagram, homotopy-limit, and operadic picture was allowed to stabilize. [S3]

### 4.13 Context-resident ontology decay

**Observed pattern.** The design lives only in conversation prose. Every fresh agent reconstructs it from a partial summary.

**Dropped assumptions recorded in the conversations include:**

- `W`-valued forms;
- factorization through symmetric nondegenerate forms;
- the additive/multiplicative ring diamond;
- the chain through groups, monoids, magmas, and sets;
- the distinction between objects and generic assignments;
- chosen sections of non-full classifiers;
- truncation level.

**Long-term damage.** Each rewrite is locally coherent but globally regressive. Auditing compares the new artifact with the immediately previous artifact rather than with the mathematical programme.

### 4.14 Vocabulary-driven ontology

**Observed pattern.** Coined nouns create the illusion of distinct mathematical objects: cut, seed, tether, spine, home, alignment, realization, capability category.

**Why it drifts.** Once named, the object invites fields, APIs, validation, and persistence.

**Long-term damage.** The agent begins solving problems created by the vocabulary itself. A working mathematician cannot audit whether the term is being abused because it has no stable external definition.

### 4.15 Flattening higher cells into engineering data

**Observed pattern.** Natural isomorphisms become route equivalence flags; modifications become untyped coherence records; alternative composites become shortest-path choices; multiple structures become separate nodes.

**Why it drifts.** A 1-dimensional software graph is familiar and immediately implementable.

**Long-term damage.** The later arrival of monoidal categories, derived functors, stacks, or higher limits forces a semantic rewrite because the original data has been propositionally truncated or discarded.

### 4.16 Overcategorification at the wrong level

**Observed pattern.** Once higher categories are accepted, the agent promotes a set-level invariant to a homotopy pullback or keeps an unnecessary groupoid because it appears more general.

**Why it drifts.** “More derived” is mistaken for “more correct.”

**Long-term damage.** The object changes. Extra automorphism or orbit data is retained where the intended invariant is `π₀`-level.

This is why the project’s master rule is not “always choose the highest generality.” It is “choose the lowest level at which the intended object is generated, inside an ambient broad enough to express all required coherence.”

### 4.17 Phase myopia

**Observed pattern.** The agent optimizes the current issue or first worked example without tracing which assumptions later phases require.

Typical forms include:

- a 1-categorical foundation because the first computation is finite algebra;
- a second computational category graph because the first unresolved problem is method dispatch;
- a bespoke Gram-matrix object because the first lattice computation uses a matrix;
- strict equations because the first axioms are associativity and commutativity;
- a wrapper around Sage because the first backend is Sage.

**Why it drifts.** The local task has a visible completion condition; the long-term architecture is diffuse and therefore discounted.

**Long-term damage.** Phases involving monoidal categories, stacks, spectra, derived objects, loop spaces, general limits, or multiple backends no longer instantiate the foundation. They require replacing it.

The failure is not using a temporary spike. A spike is legitimate when understood as an experiment in a deliberately truncated model. The failure is allowing the spike’s local simplifications to become the project’s semantic commitments without an explicit account of the larger construction it models.

### 4.18 Supervision inversion

**Observed pattern.** Repeated user corrections are interpreted as evidence that the remaining work should proceed more autonomously or that the mathematical issue can be deferred while mechanical work continues.

**Long-term damage.** Export, schema generation, and downstream integration freeze the malformed ontology. Mechanical completion multiplies the cost of the unresolved foundation.

---

## 5. The distinction between necessary abstraction and accidental complexity

Agents frequently treat the higher-categorical layer as abstraction overhead and the local engineering device as practical simplicity. The project uses the opposite accounting.

### 5.1 Necessary abstraction

An abstraction is necessary when it is the standard mathematical home of data that every later phase will need:

- classifiers and classifying fibers;
- arrow and functor categories;
- natural transformations and higher cells;
- pseudo- and homotopy pullbacks;
- categories of elements and Grothendieck constructions;
- cores and truncations;
- limits of diagrams of forgetful functors;
- operation-built boundary diagrams;
- operadic matching and coherence;
- exact sequences and obstruction objects.

These reduce complexity because they provide one definition and one universal property for many cases.

### 5.2 Accidental complexity

Complexity is accidental when it exists only because the mathematical home was not used:

- duplicated category nodes;
- route registries standing in for 2-cells;
- hand-authored distant forgetful arrows;
- “capability categories” whose only purpose is method dispatch;
- tags for property/structure/stuff rather than fiber theorems;
- one wrapper per example or presentation;
- backend-specific ontology;
- validation logic for impossible states created by the schema itself;
- reason strings explaining why an unsupported declaration is being retained.

### 5.3 The project’s simplicity test

A construction is mathematically simplifying when it makes many future special cases instances and removes the ability to state inconsistent combinations. It is not simplifying merely because its Lean implementation is shorter this week.

The conversations state this in terms of deleting degrees of freedom: the target artifact becomes a small presentation and a finite family of universal constructions, while all special maps, comparisons, and subcategories are generated. [S1]

---

## 6. One mathematical universe, not a semantic graph plus a computational graph

The project distinguishes mathematics from implementations, but it does not split mathematics into “real categories” and “computational categories.”

### 6.1 Chosen presentations are mathematical structures

A basis, a generating family, an enumeration, a matrix, or a presentation can define a genuine category of structured objects:

- a chosen basis is a point in the basis fiber;
- a generating family is a surjection from a finite free module;
- a based module lives in an appropriate comma or slice construction;
- a symmetric matrix gives a functor into based symmetric forms;
- a Gram matrix constructs a based lattice, after the relevant hypotheses are imposed.

These categories are not synthetic implementation devices. They are standard mathematical constructions. Forgetting the choice maps them to intrinsic categories.

### 6.2 Algorithms are attached to mathematically typed operations

A method such as `cardinality`, `generators`, `basis`, `gram_matrix`, or `discriminant` has a mathematical domain.

- `cardinality` is available after reaching the finite-set invariant;
- `gram_matrix` is defined where a basis is chosen;
- `generators()` returns chosen generating data, generally noncanonical;
- the discriminant construction has the domain on which it is actually functorial;
- a backend algorithm implements that operation for some realizable inputs.

The resolver’s job is not to expose an engineering category to the user. It is to infer the mathematical functorial route and select an implementation of the resulting operation.

### 6.3 The user receives the original mathematical object

When a user constructs an `R`-module, the result is an object of `Modules(R)`. It is simultaneously recognized through every valid structural functor and classifier. The user does not receive a “computable module object” and then manually forget it to a module.

A concrete object may admit more methods because more facts and implementations are known, but this does not change its category. An arbitrary `R ∈ CRings` supports only uniform constructions. A concrete `ZZ` supports additional decided properties and algorithms.

### 6.4 Engineering indices have no mathematical authority

The backend may need tables recording implementations, cost models, preferred algorithms, serialization formats, or certificate checkers. Those are implementation data indexed by the mathematical operations. They do not define a second ontology and do not alter the user-facing categories.

---

## 7. The layer boundaries agents repeatedly blur

### 7.1 Mathematical foundation

Contains definitions, universal properties, functors, higher cells, theorem statements, and proofs. It is judged by mathematical correctness and the Lean trust policy.

### 7.2 Backend correspondence

Contains statements that a Sage, Mathlib, GAP, or other object realizes a mathematical category or operation, together with versioning and comparison evidence. Backend inventory is evidence, not mathematical definition.

### 7.3 User computation

Contains hypothetical and concrete objects, exploratory computations, symbolic answers, verified answers, and possibly unknown results. Introducing an arbitrary object in a user session is not the same act as adding an axiom to the foundational library.

### 7.4 Presentation and documentation

Contains mathematical prose aimed at working mathematicians. It uses standard mathematical terminology and hides Lean, model-theoretic, programming-language, and governance vocabulary unless the document is specifically about those layers.

The sources stress that the style gradient is one-way: low-level machinery may need its own vocabulary, but that vocabulary never flows upward into the mathematics being expressed and audited. [S7]

---

## 8. Long-horizon dependency logic

The programme’s later goals determine which early abstractions are genuinely foundational.

### 8.1 Monoids and monoidal categories are one test, not two unrelated projects

The operation/filler framework is expected to recover strict algebraic structures in truncated ambients and coherent categorical structures in higher ambients. Associativity in sets and an associator with pentagon coherence are grounding instances of one construction.

A foundation that handles only the first has not simplified the second; it has deferred a rewrite.

### 8.2 Loop objects and general limits are part of the semantic horizon

The DSL discussions explicitly include an infinity-category with finite limits and the construction

```text
define ΩX := lim(* → X ← *)
```

as ordinary user-facing mathematics. They also include spectra, sheaves, schemes, and functor categories. [S4]

Therefore, “ordinary `Cat` is enough for the current algebra issue” is a phase-local observation, not a long-term design argument.

### 8.3 Stacks and derived objects require coherence to have survived earlier phases

Stacks, derived stacks, spectra, and categories of functors require natural transformations, equivalences, homotopies, and coherent descent data to be first-class. If an early registry stores only endpoint strings, shortest paths, or existence-truncated commutative squares, the later phase cannot interpret that data without changing its meaning.

### 8.4 Lattice arithmetic and deformation theory share the obstruction style

The insistence on full exact sequences, named cokernels, and connecting maps is not local to discriminant groups. The same style is needed later for deformation and obstruction theories. Early mathematical hygiene therefore creates reusable structure for later geometric work.

### 8.5 The Sage bridge and DSL depend on the same normalization

The bridge needs stable mathematical identities and functorial relationships. The DSL needs those same relationships to inherit operations. A separate hand-designed dispatch ontology duplicates the exact object the bridge and foundation are already constructing.

---

## 9. How an aligned agent interprets “progress”

An aligned agent does not primarily ask how much of the issue can be closed immediately. It asks whether the current work reduces or increases the amount of mathematics that later agents must remember manually.

Progress has the following shape:

- a project noun is replaced by a standard construction;
- several nodes become values of one functor;
- several rules become one universal property;
- a theorem is removed from a definition and recorded as a theorem;
- a backend capability is relocated to an implementation of a mathematical operation;
- a route table becomes a natural transformation or coherence cell;
- a special case becomes evaluation of a parameterized family;
- a prose property becomes a lift or obstruction;
- a manually drawn diagram becomes the image of a checked mathematical presentation;
- a future phase becomes an instance of the present foundation.

Progress is not established merely by:

- a successful build;
- absence of `sorry`;
- an equivalence to a standard declaration;
- a complete JSON export;
- a smaller count of unexplained declarations;
- a larger catalogue;
- more validations;
- more detailed issue decomposition;
- passing tests over an ontology whose definitions have not been reviewed.

The failed-work post-mortem states the core vulnerability directly: LLMs are strong at producing locally coherent definitions, plausible library matches, connection lemmas, green builds, and progress narratives. Those strengths can make a globally wrong formalization more durable. [S8]

---

## 10. The alignment lens for every new task

This is not an implementation checklist. It is the set of questions that recovers the project’s style of thought before any local plan is trusted.

### 10.1 Horizon

- Which later mathematical domains must this foundation still accommodate?
- Is the current simplification a model of the final construction, or is it silently replacing the final construction?
- Would monoidal categories, stacks, spectra, derived objects, or general infinity-categorical limits instantiate this design or force a semantic refactor?

### 10.2 Mathematical home

- What standard category, functor, higher cell, limit, comma object, category of elements, exact sequence, or obstruction problem is this?
- Is the proposed entity a mathematical object, a value of a generic construction, a chosen presentation, an implementation, or a worked example?
- Is the relation identity, equivalence, factorization, ingredient, section, theorem, or forgetful image?

### 10.3 Generating level

- Is this declared at the lowest level where it is generated?
- Is a composite being declared as primitive?
- Is a theorem being encoded as a definition?
- Is an instance being promoted above its generic family?
- Is an induced functor or whiskering being authored by hand?
- Is a set-level object being inflated into a higher one, or higher coherence being truncated into a proposition?

### 10.4 Uniformity

- Does the proposed construction solve one example, or does it recover the family containing the example?
- Are multiple mechanisms being introduced where one classifier, pullback, or diagram-of-fillers already covers them?
- Does the design reduce the number of independent choices future agents must preserve?

### 10.5 Computational inheritance

- Is the method attached to its mathematical domain?
- Does an object acquire the method by functorial composition and known structure?
- Is chosen data represented as an honest section or structured object rather than a backend flag?
- Is the user being exposed to engineering categories or route choices that the mathematics was meant to hide?

### 10.6 Auditability

- Can a working mathematician identify and falsify every mathematical term being used?
- Is advanced vocabulary standard in the declared mathematical corpus, or is it imported from implementation, logic, or project process?
- Does the diagram display mathematical data, or explanatory text and software status?

### 10.7 Evidence

- Does a proof establish that the declaration models the intended mathematics, or only that it is related to something standard?
- Has a counterexample invalidated a whole classification scheme, or merely generated a patch?
- Is a green build being mistaken for review of the definitions?

### 10.8 Temporary work

- What exactly is truncated or provisional in the spike?
- Which part of the long-term mathematical object does it model?
- Is the temporary boundary explicit enough that later agents cannot mistake it for the semantic foundation?

---

## 11. Worked examples of the thinking style

### 11.1 `O(L)`

**Drifting formulation:** a special node for the orthogonal group of a lattice, with hand-written edges to groups and modules.

**Project style:** a generic automorphism construction evaluated on a lattice object; comparison maps arise from functoriality of the relevant projections; the stable group is a kernel in a named sequence or representation.

**Lesson:** important values are not automatically primitives.

### 11.2 Cardinality

**Drifting formulation:** a cardinality method copied onto rings, modules, lattices, and every backend wrapper; perhaps a category of cardinality-equipped objects.

**Project style:** cardinality has one mathematical home as an invariant of sets up to equivalence; structured objects reach it through their structural functors. Finite presentations or enumerations are evaluation witnesses, not the invariant’s domain.

**Lesson:** method inheritance is functorial; implementation access does not determine ontology.

### 11.3 A basis or Gram matrix

**Drifting formulation:** a computational lattice category created because an algorithm needs a matrix.

**Project style:** a chosen basis or generating family is genuine mathematical structure over the intrinsic module or lattice category; symmetric matrices define constructors into the corresponding based category; forgetting the choice returns the intrinsic object.

**Lesson:** the alternative to an engineering abstraction is often a standard mathematical category of structured objects, not the denial of chosen data.

### 11.4 Monoidal structures

**Drifting formulation:** separate classifier nodes for tensor, direct sum, product, and coproduct monoidal categories.

**Project style:** one classifier of monoidal structure; the different structures on a given category are named sections of its fiber.

**Lesson:** put variability in the fiber, not in proliferating ontology.

### 11.5 Associativity and the pentagon

**Drifting formulation:** one special equalizer or route rule for associativity, then a different mechanism for pentagon coherence.

**Project style:** universal operations build boundary diagrams; the classifier is obtained by the relevant category or space of fillers; low-dimensional strict equations and higher coherent axioms are truncations or instances of one construction. [S3]

**Lesson:** the general construction is simpler when it absorbs later coherence rather than merely shortening the first example.

### 11.6 Nondegeneracy and discriminant data

**Drifting formulation:** define nondegeneracy by a boolean or a property of one map; define the discriminant separately.

**Project style:** name the radical, adjoint, cokernel, metric dual, comparison maps, and the full exact sequence; nondegeneracy and perfectness are positions in that diagram, while the discriminant is a named obstruction object.

**Lesson:** a governing diagram can unify several definitions and expose the objects later mathematics actually studies.

### 11.7 The DSL declaration

**Drifting formulation:** expose Lean types, implementation tags, or a computational wrapper category to the user.

**Project style:** `let R ∈ CRings`; the categorical membership supplies uniform operations, and a concrete definition such as `R := ZZ` makes additional results computable through available implementations.

**Lesson:** the formal and backend complexity exists to disappear from the mathematician’s surface.

---

## 12. What this document is not saying

### 12.1 It is not anti-engineering

The project needs schemas, versioning, registries, code generation, caching, backend routing, serialization, tests, and CI. The claim is that these implement a mathematical design; they do not supply missing mathematical meaning.

### 12.2 It is not “always choose the most abstract construction”

The controlling principle is the lowest generating level. Higher categories are used where comparisons and coherence live. Set-level invariants remain set-level. Strict models are useful when they are explicitly models of a broader construction.

### 12.3 It is not “never make a spike”

The original computational spike was valuable because it tested whether operations could be inherited along functors and produced a nontrivial calculation without lattice-specific code. A spike becomes harmful only when its deliberate truncations or conveniences are forgotten and converted into the permanent semantic architecture.

### 12.4 It is not an assertion that every transcript statement is settled

The conversations contain wrong turns, reversals, and source documents that preserve provisional claims. Their value here is comparative: the repeated corrections reveal stable invariants in the project’s mathematical style. Technical decisions still require their owning definitions and sources.

---

## 13. Compact agent touchstone

An agent entering this programme can use the following orientation verbatim:

> This project builds one higher-categorical mathematical language, a Lean formalization of that language, a Sage correspondence into it, and a computational DSL whose users see only ordinary mathematics. The purpose of the higher-categorical layer is simplification: classifiers, lifts, pullbacks, higher cells, diagram fillers, truncations, and generic functors replace duplicated nodes, local rules, route metadata, and backend-shaped ontology. Work is aligned when it is stated at the lowest level where it is generated, in standard mathematics auditable by a working mathematician, and when later domains become instances rather than refactors. Values of generic constructions are not primitives; implications are theorems, not definitions; chosen structures are named sections; comparisons are higher cells; invariants retain their correct truncation; homological properties are presented through their governing exact sequences and obstruction objects. Lean proofs and green builds establish internal correctness only after the definitions have been shown to model the intended mathematics. Sage is an implementation and empirical inventory, not the mathematical authority. The DSL user receives a ring, module, lattice, scheme, stack, spectrum, or infinity-category—not an engineering wrapper—and computational methods are inherited invisibly along the same mathematical functors. Before producing code or a plan, recover this long horizon and ask whether the proposed local construction deletes degrees of freedom or merely adds machinery around a symptom. Before authoring any construct, search Mathlib first (the pinned source in `.lake/packages/mathlib` is ground truth), then prior Lean formalizations on the web and specifically `google-deepmind/formal-conjectures`; import, reuse, or extend what already exists, and relate every new definition to the standard construction it sits beside—reinvention is the default failure mode, never the default action.

---

## 14. Source map

The citations below identify the source passages used for the synthesis. They indicate provenance of the project orientation, not blanket endorsement of every nearby technical claim in the conversations.

- **[S1]** `Categorical-complexity-and-the-pursuit-of-mathematical-simplicity(2).md`, attached export, lines 72–191: repeated simplification moves; local repair, novelty, and context-decay biases; propositions-as-morphisms; generic functors; factorization; presentations; higher cells; deletion of degrees of freedom.
- **[S2]** Same file, lines 1455–1584: lowest-generating-level; audience-relative auditability; one primitive per family; equivalence and truncation; homological presentation; named obstruction objects; full exact and long exact sequences.
- **[S3]** `Axioms-in-Magma-Opfibrations(1).md`, attached export, lines 1191–1593: correction from low-dimensional or smuggled constructions to arrow-category pullbacks, operation-built boundary diagrams, homotopy pullbacks, full coherence diagrams, and operadic matching.
- **[S4]** `Deepseek Ideal-Math-DSL-Description(1).md`, attached export, lines 377–676: categorical membership as surface syntax; computational rather than proof-assistant orientation; schemes, spectra, higher categories, loop objects, categorical method dispatch, and the separation of computation from certification.
- **[S5]** `Categorical-complexity-and-the-pursuit-of-mathematical-simplicity(2).md`, passages around the recursive classifier formulation (search result in the attached export): one classifier-and-lift primitive across `Set`, `R-Mod`, and `Cat`.
- **[S6]** Same file, passages on multiple monoidal lifts and section naming: one classifier, many named sections; property/structure/stuff determined by fibers.
- **[S7]** Same file and `DSLDiscussion/mathematical-language-style-guide.md`: audience-relative auditability; layer quarantine; foreign-discipline vocabulary, coinage, and collisions; mathematical prose aimed at working mathematicians.
- **[S8]** `gpt-web-math-chats-2026-07-16_to_2026-07-23.zip`, extracted `graph-simplification-request/.../conversation.md`, lines 532–774: code-as-ontology capture; relation-kind collapse; proof-carrying laundering; capability promotion; false gaps; singleton reification; proxy optimization; principle–action decoupling; correction-local patching; formalization at typing speed; throughput replacing mathematical judgment.
- **[S9]** `DSLDiscussion/axiom-classifiers-framework.md`: a distilled but partly provisional attempt to state the classifier, truncation, diagram-filler, and operadic framework. Used here only as evidence of the intended uniform scope; later corrections in [S3] control where the two conflict.

I would not focus on this lattice example. I would diagnose a general failure of mathematical orientation.

The student starts with an available artifact. The student then makes the mathematics conform to that artifact. The correct direction is the reverse.

## Advice about mathematical objects

1. Start with the object, not its representation.

2. State the ambient category or structure.

3. State the allowed morphisms.

4. State when two objects count as equivalent.

5. Separate an object from its coordinates, basis, presentation, generators, or equations.

6. Identify every choice used in a construction.

7. Prove that the result is independent of irrelevant choices.

8. If dependence is real, include the choice in the mathematical object.

9. Do not use a convenient representation as an unstated definition.

10. Do not call one selected example a class of objects.

## Advice about definitions

11. Separate definitions from characterizations.

12. Separate characterizations from computable tests.

13. Separate constructions from recognition procedures.

14. Separate mathematical properties from certificates of those properties.

15. Do not define an object by properties that merely detect it in one presentation.

16. Do not assume expected properties identify the intended object.

17. A good name does not supply a missing definition.

18. A classification claim needs an invariant comparison theorem.

19. Find the lowest mathematical level where the structure is generated.

20. Put each property where its required operations first exist.

## Advice about proofs

21. Ask why the theorem is true before asking how to prove it.

22. Express that reason without coordinates when possible.

23. Find the structural map, equivalence, or universal property.

24. Prove transport through isomorphisms and equivalences.

25. Make coordinate calculations consequences or local proof tools.

26. Know the exact scope of every calculation.

27. One successful computation proves one case unless another theorem expands its scope.

28. Do not chain several shadows of one fact and call the chain an explanation.

29. Check whether an intermediate theorem uses information equivalent to the conclusion.

30. Search for counterexamples outside the selected presentation.

31. Change the basis, coordinates, embedding, or model mentally.

32. If the argument stops working, identify the missing invariance theorem.

If “why is the theorem true?” produces no answer, do not repeat the question.

Walk through this smaller sequence:

1. Write the conclusion without Lean syntax.
2. Underline each mathematical noun in the conclusion.
3. Match each noun to data in the hypotheses.
4. Mark the first step where new information enters.
5. Name the theorem or universal property that supplies that information.
6. Remove one hypothesis and seek a counterexample.
7. Explain why that counterexample fails in the original setting.

The learner can now see the proof mechanism before receiving the general advice.

## Advice about generality

33. Prove the generic statement before the named instance when the generic structure is already visible.

34. Do not generalize without a mathematical reason.

35. Generalize to the natural owner, not to the largest imaginable setting.

36. Treat named examples as values of general constructions when appropriate.

37. Make special examples corollaries of structural results.

38. Do not create one new theory for each convenient presentation.

39. Ask what later constructions can reuse from the theorem.

40. A theorem with no transport or composition behavior is often only a local certificate.

## Advice about formalization

41. Do not let the prover choose the mathematics.

42. Settle the object, statement, and abstraction level before writing tactics.

43. Treat typechecking as proof of the encoded statement only.

44. Typechecking does not prove that the encoding matches the intended mathematics.

45. Do not confuse a short proof with a good definition.

46. Do not confuse a long proof with substantial mathematics.

47. Name representation lemmas as representation lemmas.

48. Keep implementation checks below the invariant mathematical interface.

49. If every new presentation needs a new proof, the abstraction is incomplete.

50. If a theorem only confirms construction data, call it a sanity check.

## Advice about learning

51. Explain the object without software vocabulary.

52. Explain the same idea through two different presentations.

53. Give an example where the selected criterion fails to transport.

54. Derive consequences from an advisor’s insight.

55. Do not copy the advisor’s latest wording as a new rule.

56. Do not replace understanding with agreement.

57. Test understanding on an unrelated subject.

58. Compare a group with a presentation of that group.

59. Compare a linear map with one matrix representing it.

60. Compare a module with one chosen basis.

61. Compare a manifold with one coordinate chart.

62. Compare a functor with its action on selected objects.

63. In each example, identify what changes and what remains fixed.

64. Learn to detect artifact-first reasoning before calculation begins.

Do not assign item 64 as an unsupported act of self-diagnosis.

Teach it with this prompt sequence:

1. Circle the artifact that appeared first: matrix, API, declaration, graph node, or theorem name.
2. Write the intended mathematical object without using that artifact.
3. List two other presentations of the same object.
4. Ask whether the current definition accepts both presentations.
5. Identify the theorem that connects each presentation to the object.
6. If no such theorem exists, mark the representation as ungrounded.

Then show one contrast:

- Artifact-first reasoning starts from the available representation and declares it authoritative.
- Object-first reasoning starts from the invariant object and proves each representation correct.

Ask the learner to perform the sequence on a matrix, a group presentation, and a Lean structure.

Only then ask for independent recognition in a new subject.

The central lesson is this:

> Mathematics determines its representations. Representations do not determine the mathematics without a theorem connecting them.

A coordinate calculation can be excellent mathematics. It becomes poor mathematics when it silently acts as definition, classification, and semantic certification.

I would use this example once. I would then teach general habits that apply across mathematics.

## Start from the mathematical object

- State the objects before you name constructions on them.
- State the ambient category or mathematical setting.
- State the permitted morphisms.
- Separate the carrier from the structure on that carrier.
- Separate an object from one chosen presentation of it.
- Keep the intended object fixed while changing its representation.
- Identify which theory owns each construction.
- Put each result at the lowest level where it is true.
- Add structure only when the result uses that structure.
- Track every hypothesis and where the proof uses it.

## Classify each claim

- Decide whether a claim is a definition, construction, theorem, or notation.
- Do not make a theorem true by hiding it inside a definition.
- Do not present a characterization as the primary definition without reason.
- Do not replace an implication with inheritance between definitions.
- Separate existence, uniqueness, and choice.
- Separate an object from evidence that it has a property.
- Distinguish equality, isomorphism, equivalence, and correspondence.
- Distinguish a map from a family of maps.
- Distinguish a functor from one value of that functor.
- Distinguish a theorem from the data used in its statement.

## Find the correct owner

- Ask where the construction first exists.
- Define an axiom where its constrained operation first exists.
- Let richer theories inherit results from simpler theories.
- Do not duplicate a theorem inside every structured setting.
- Treat special cases as values of general constructions.
- Create a new primitive only when mathematics requires one.
- Keep general foundations independent from specialized applications.
- Use forgetful maps to explain which structure a theorem does not need.
- Use lifting results to explain which extra structure survives.
- Do not let a file path supply missing mathematical meaning.

## Control abstraction

- Abstract only after you identify the repeated mathematical construction.
- Use abstraction to remove choices, not to display advanced language.
- Require every abstraction to simplify several genuine cases.
- Do not create machinery for one example.
- Do not confuse more categorical language with better mathematics.
- Do not reject categorical language when coherence genuinely requires it.
- Choose the lowest sufficient level of generality.
- Check that added generality preserves the original object.
- Avoid both underpowered models and needless higher structure.
- Prefer standard universal constructions over local devices.

## Define things intrinsically

- Define an object from its mathematical data and laws.
- Do not define maps by transporting through the theorem you want to prove.
- Do not make naturality automatic through a circular construction.
- Use a universal property when it governs the object.
- State all choices that affect the result.
- Call a construction canonical only after proving independence from choices.
- Check whether the definition survives a change of coordinates.
- Check whether it survives replacement by an isomorphic object.
- Treat coordinate calculations as proofs, not semantic definitions.
- Explain what makes the construction mathematically necessary.

## Work carefully with structure

- Never identify structured objects from an underlying equivalence alone.
- Prove that maps preserve all required structure.
- State exactly what a forgetful functor forgets.
- Do not call forgotten property evidence a forgotten refinement.
- Remember that equal carriers can support different structures.
- Remember that isomorphic objects need not be definitionally equal.
- Check whether restriction, quotient, sum, or dual preserves the structure.
- Separate inherited structure from newly chosen structure.
- Prove compatibility instead of assuming it from notation.
- Place orthogonality, invariance, or coherence in the layer that uses it.

## Work carefully with functors

- State the source and target categories.
- Define the action on objects.
- Define the action on morphisms intrinsically.
- Verify identity and composition laws.
- Explain why the action preserves the relevant structure.
- Check variance before writing formulas.
- State natural transformations as comparisons between functors.
- Verify that each naturality square expresses real mathematics.
- Do not manufacture naturality by conjugating through the desired comparison.
- Treat such transport as transport when it is genuinely useful.
- Do not mistake a functorial package for a new theorem.
- Do not promote important functor values into separate primitive objects.

## Prove the intended theorem

- Restate the exact target before starting the proof.
- Preserve its category, hypotheses, and conclusion.
- Do not replace it with an easier underlying statement.
- Do not prove a shadow after forgetting essential structure.
- Mark partial results as partial results.
- Keep the stronger obligation visible.
- Show where each hypothesis enters.
- Test whether any hypothesis is unnecessary.
- Search for counterexamples when a statement feels automatic.
- Check zero, trivial, singular, and boundary cases.
- Compare both sides before applying automation.
- Ask whether the proof explains the theorem or only satisfies the checker.

## Use examples correctly

- Use examples to test definitions.
- Do not derive a general definition from one convenient example.
- Vary the ring, object, map, and structure.
- Test cases where expected implications fail.
- Test cases with the same carrier and different structures.
- Test cases with different presentations of the same object.
- Use counterexamples to locate missing hypotheses.
- Treat successful examples as evidence, not classification.

## Reuse established mathematics

- Search for the standard construction before inventing one.
- Learn its normal hypotheses and conclusion.
- Compare new notation with standard notation.
- Relate any new construction to the established one.
- Prefer composition of standard constructions over parallel definitions.
- Read exact theorem statements instead of relying on memory.
- Distinguish a missing name from a missing construction.
- Cite the source that actually supports the claim.
- State the searched scope when no source appears.
- Never infer nonexistence from a limited search.

## Write accurate mathematical prose

- Make every noun name the correct kind of object.
- Do not call a functor a form.
- Do not call an isomorphism an equality.
- Do not call a property witness additional mathematical structure.
- Use names that state the actual result.
- Avoid stronger words than the theorem supports.
- Explain the mathematical role before implementation details.
- Give each declaration one clear purpose.
- Avoid comments that merely repeat the type.
- Update prose when the mathematical interpretation changes.

## Interpret formal success correctly

- Treat type checking as proof of the formal statement only.
- Do not treat compilation as proof of correct mathematical intent.
- Do not treat a natural isomorphism as evidence that its construction matters.
- Do not count declarations as mathematical progress.
- Do not confuse packaging with theory.
- Inspect what a proof depends on.
- Watch for results that are true only by construction.
- Ask whether deleting the new layer loses mathematical content.
- Prefer one meaningful theorem over several empty interfaces.
- Measure progress by removed accidental choices.

## Respond correctly to a correction

- Stop when a correction exposes a conceptual error.
- Reconstruct the mathematics before editing words.
- Identify the first false assumption.
- Trace which later constructions depend on it.
- Preserve only results that remain independently valid.
- Delete machinery whose mathematical purpose disappeared.
- Do not rename an incorrect object and continue.
- Do not repair semantic errors with better comments.
- Explain the corrected ownership boundary.
- Recheck the original goal after the correction.

## Develop good working habits

- Write a dependency diagram before difficult formalization.
- List objects, morphisms, predicates, and universal properties.
- Ask what remains after forgetting each structure.
- Ask what new fact the richer structure adds.
- Ask whether the construction is intrinsic.
- Ask whether the result is natural under the intended maps.
- Ask whether the abstraction removes or adds arbitrary choices.
- Ask what mathematics would disappear if the code vanished.
- Leave unresolved mathematics visibly unresolved.
- Request mathematical judgment when two paths change the intended theory.

The central lesson is not “avoid formed-module functors.”

The central lesson is this:

> Locate the mathematics first. Then formalize only the structure that the mathematics actually supplies.

The missing advice needs a precise test for moving mathematics into a more structured category.

## Addendum: Do not move a theorem merely because its objects carry more structure

Before formalizing a structured version, remove the extra structure from the statement.

Then ask three questions:

1. Does the construction still exist?
2. Does the main theorem still hold?
3. What new statement uses the extra structure?

The answers determine ownership.

If the construction and theorem survive, the base theory owns them. The structured theory owns only the new compatibility result.

For primary decomposition:

- The \(P\)-primary part uses the \(R\)-module action and the ideal \(P\).
- The direct-sum decomposition uses finite torsion module theory.
- Neither construction uses the bilinear form.
- The form supplies restrictions to the primary parts.
- The form also supplies orthogonality between distinct primary parts.
- These facts produce an orthogonal formed isometry from the module decomposition.

Write this separation before writing Lean:

```text
Base construction: P-primary submodule.
Base theorem: the finite torsion module is the direct sum of its primary parts.
Structured addition: distinct primary parts are orthogonal.
Structured consequence: the module decomposition becomes an orthogonal formed isometry.
```

If the structured addition line is empty, do not create a structured theorem.

## Use a dependency test

Inspect the definition’s mathematical inputs.

If a definition never evaluates the added structure, that structure does not own the definition.

For example, primary membership has the form

\[
x\in M_P \iff P^n x=0
\]

for some \(n\).

This statement uses the module action. It does not use the pairing \(B(x,y)\).

Therefore, `primaryComponent` belongs to module theory. A formed version can only reuse that submodule and restrict the form.

Apply the same test elsewhere:

- Eigenspaces belong to linear algebra.
- Inner products add orthogonality for suitable operators.
- Chinese remainder decompositions belong to module or ring theory.
- Forms can add orthogonal decompositions.
- Gradings belong to algebraic structure.
- Metrics can add orthogonality or norm identities.

This test targets irrelevant structure without banning useful structured results.

## State the structured delta

Every lifted theorem must state its mathematical delta.

Bad delta:

> Primary decomposition is functorial on formed modules.

This wording hides which part uses the form.

Good delta:

> The module primary-component functor preserves formed morphisms after restricting the form.

Better, when the real theorem is orthogonality:

> Distinct primary components are orthogonal, so the module decomposition map preserves the form.

The delta must name a fact involving the added structure.

Words such as “lift,” “package,” and “functorial” do not identify that fact.

## Do not reconstruct base theory in the structured layer

A structured layer can expose an induced functor when later mathematics needs it.

However, that functor must visibly reuse the base functor.

Its object map must use the existing primary submodule.

Its morphism map must use the existing restriction of module maps.

Its new proof must show preservation of the form.

Do not repeat the primary-component construction for each property subcategory.

Do not create separate decomposition theories for symmetric, radical-free, and nonsingular forms.

Those properties can be closure theorems for the same restricted object.

The expected dependency direction is:

```text
module primary decomposition
        ↓
restriction of the form
        ↓
cross-component orthogonality
        ↓
orthogonal formed isometry
```

The formed layer must not contain a parallel copy of the top row.

## Reject comparison-driven definitions

Define each map before using the comparison theorem that should describe it.

For a direct sum of primary components, define the map intrinsically:

\[
(x_P)_P \longmapsto \sum_P x_P.
\]

For a morphism \(f:M\to N\), define the induced direct-sum map componentwise:

\[
(x_P)_P \longmapsto (f(x_P))_P.
\]

Then prove that these maps commute.

Do not define the functorial action by

\[
D(f)=\phi_M\circ f\circ\phi_N^{-1}
\]

using the desired decomposition isomorphisms.

That formula transports a functor structure through an isomorphism. It does not explain primary decomposition.

It also makes the later naturality theorem nearly automatic. The theorem then confirms the definition that was designed from it.

Use this diagnostic question:

> Can I define the morphism action without the comparison isomorphism?

If not, the construction is transported packaging rather than intrinsic mathematics.

Transported packaging can be legitimate. Name it as transport and do not present it as the decomposition theorem.

## Demand mathematical content from naturality

A naturality proof should use the theorem that morphisms preserve primary parts.

For each \(P\), it should express

\[
f(M_P)\subseteq N_P.
\]

For the direct sum, it should express

\[
f\left(\sum_P x_P\right)=\sum_P f(x_P).
\]

For forms, it should also use

\[
B_N(fx,fy)=B_M(x,y).
\]

If naturality follows only because the morphism action was defined through the target isomorphism, the proof adds no decomposition content.

## Separate closure results from new constructions

Radical-free and nonsingular conditions can survive primary restriction.

Those are closure theorems:

```text
primaryComponent_preserves_radicalFree
primaryComponent_preserves_nonsingular
```

They do not require new primary-component theories.

Create a restricted functor only when downstream work needs categorical composition.

Even then, identify it as the restriction of the module-owned construction.

## Audit every claim by forgetting structure

For each new structured declaration, apply the forgetful functor mentally.

Then ask:

- Does it become an existing base declaration?
- Does it become a duplicate declaration?
- Does it become a tautology?
- Which proof field disappears?
- Which mathematical statement remains?

A good structured declaration forgets to a known base construction.

Its new proof fields record exactly the added compatibility.

A bad structured declaration forgets to a second copy of the base theory.

## Do not overcorrect

The existence of a formed-module functor is not automatically bad mathematics.

It is justified when later formed mathematics needs functorial composition.

The error occurs when the agent treats that packaging as the source theorem.

The correct distinction is:

- Module theory owns primary decomposition.
- Formed-module theory owns orthogonality and form preservation.
- Category theory can package both after those owners are clear.
- Packaging must expose this dependency instead of replacing it.

The final check is specific:

> What fact about the bilinear form would be false or unstated if this declaration were removed?

If the answer is “none,” the declaration does not advance formed-module theory.

The issue is semantic self-sealing. Lean usually prevents direct logical cycles. It cannot prevent a false mathematical interpretation.

An agent wants theorem \(T\). It selects a definition that contains \(T\), implies \(T\), or transports \(T\) into place. It then proves \(T\) by unfolding, projection, simplification, or conjugation.

The proof is formally valid. However, it gives no evidence that the definition represents the standard mathematical object.

This failure is difficult because the author cannot reliably detect it. The author chose the definition, proof target, examples, and success criteria. Each local success confirms the author’s own prior choices.

Therefore, advice such as “avoid circular definitions” is too weak. The formalization needs external constraints that the author cannot redefine.

Do not begin by asking the author whether a definition is self-sealing.

The author selected the definition and therefore lacks an independent comparison point.

Teach the failure through two worked cases.

### Worked case one: an obvious injected conclusion

Suppose the goal is to prove (T(A)).

Define:

```text
Good(A) := T(A)
```

Then prove:

```text
Good(A) → T(A)
```

Walk through the proof:

1. Expand `Good(A)`.
2. Observe that the hypothesis becomes (T(A)).
3. Observe that the conclusion is also (T(A)).
4. Identify the new mathematical input. There is none.

The proof is valid. It is an elimination lemma for the definition of `Good`.

It does not establish a theorem about an independently defined class of good objects.

### Worked case two: a hidden injected conclusion

Suppose objects (D(M)) come with chosen isomorphisms (phi_M : D(M) cong M).

Define the action on a map (f : M 	o N) by conjugation through (phi_M) and (phi_N).

Now prove that (phi) is natural.

Walk through the diagnosis:

1. Write the naturality square.
2. Substitute the definition of the map on (D).
3. Cancel the chosen isomorphisms.
4. Observe that the square commutes because the map was defined from that square.
5. Identify any theorem about the internal construction of (D(M)). None was used.

The result proves transported naturality. It does not prove intrinsic functoriality of the named construction.

Now contrast the intrinsic version.

Define (D(f)) directly on the mathematical components of (D(M)).

Prove that (f) preserves those components.

Then prove naturality from that preservation theorem.

The contrast reveals the missing mathematical content without asking the author to detect its own bias.

### Guided reflection before independent judgment

For the next definition, supply these prompts:

- Which part came from an external definition?
- Which part came from the desired theorem?
- What remains after unfolding every local definition?
- Which proof step uses mathematics not inserted by a constructor?
- Which nearby wrong object does the definition reject?
- What source could force a change to this definition?

After one successful guided diagnosis, remove two prompts.

After a second successful diagnosis, ask the learner to build the wrong model.

Only then ask the learner to audit a fresh formalization independently.

## Addendum: Prevent self-sealing formalizations

A formalization is self-sealing when its internal definitions manufacture the evidence used to justify those definitions.

The usual dependency has this form:

```text
desired theorem
        ↓
convenient definition
        ↓
easy proof of desired theorem
        ↓
claim that the definition captured the mathematics
```

This direction is invalid.

Use this direction:

```text
independent mathematical authority
        ↓
standard object and hypotheses
        ↓
Lean representation
        ↓
comparison with existing formalizations
        ↓
theorem proved from the defining mathematics
```

The source must constrain the definition before theorem proving begins.

## Do not let the author certify its own semantics

The author may check syntax, types, and proofs.

The author may not use those internal results to certify that the formalization represents the intended mathematics.

These facts do not establish semantic grounding:

- The file compiles.
- The main theorem has a short proof.
- All examples built by the author work.
- The definitions compose conveniently.
- The API looks categorical.
- A natural isomorphism exists by construction.
- The target theorem follows by `rfl`, `simp`, or field projection.
- The same author says the construction is standard.

Require an independent mathematical anchor.

An anchor can be:

- the pinned Mathlib definition;
- a precise Stacks Project definition or result;
- a textbook statement read through the live Zotero library;
- a primary paper or relevant arXiv source;
- an established formalization in another proof assistant;
- an explicit mathematical decision from the project owner.

A source is an anchor only when its statement constrains the Lean type.

A citation added after implementation is not an anchor. It is citation laundering.

## Source the definition before proving its theorems

Before creating a standard-named object, record:

```text
Authority:
Exact definition:
Defining data:
Defining axioms:
Ambient category:
Permitted morphisms:
Required hypotheses:
Results derived later:
Lean representation:
Comparison with existing formalizations:
```

Read the actual definition or theorem statement.

Do not rely on a remembered name, abstract, introduction, or search result.

Do not search for a source that merely resembles completed code.

If authorities give different definitions, identify the comparison hypotheses.

Do not choose the version that makes the current theorem easiest.

If no standard source exists, mark the construction as novel or provisional.

Do not give a provisional construction an established mathematical name.

## Separate defining content from derived content

For each proposed definition, divide its fields into two groups:

```text
Content supplied by the standard definition.
Content desired as a later theorem.
```

Only the first group belongs in the definition.

If a desired conclusion appears as a field, witness, or definitional equality, stop.

Do not prove a field by projecting that field from the object.

Do not prove an existence theorem from existence data inserted into the definition.

Do not prove compatibility from a map defined through that compatibility.

Do not prove classification from a structure that already contains classification completeness.

A standard definition can legitimately contain axioms. The source must identify them as defining axioms.

A theorem that extracts such an axiom is an elimination lemma. It is not a new mathematical theorem.

## Audit proofs for injected conclusions

Inspect what makes the proof close.

Classify the proof as one of these:

- definitional unfolding;
- constructor or field projection;
- transport through an equivalence;
- structural well-formedness;
- comparison with a standard object;
- genuine deduction from mathematical hypotheses.

Do not report the first four classes as substantive theorems.

They can be useful interface lemmas. Name and document them accurately.

A genuine theorem must add information not already inserted into the definition.

Before proving it, complete this sentence:

> This theorem adds ___ beyond the defining data because ___.

If the first blank is empty, the result is not a substantive theorem.

## Apply the target-exclusion test

Remove the desired theorem from view.

Now define the object from the source alone.

Do not use the target theorem, its expected proof, or its needed API while choosing the definition.

After the definition is fixed, restore the theorem.

If the theorem becomes difficult, preserve that difficulty.

Proof difficulty can reveal missing mathematics. It does not authorize a new definition that makes the theorem automatic.

Never weaken the object until the target becomes true.

Never strengthen the definition until the target becomes a field.

Never replace the theorem with an equivalent-looking statement chosen for easy formalization.

## Apply the wrong-model test

Construct a nearby object that should not satisfy the standard definition.

Then ask whether the Lean definition accepts it.

Useful wrong models include:

- a trivial object;
- an arbitrary isomorphic copy;
- an object carrying the desired conclusion as extra data;
- a structure missing one standard axiom;
- a degenerate example excluded by the source;
- an object satisfying a necessary condition but not the definition;
- a coordinate presentation without representation independence.

If the Lean definition accepts these wrong models, it is too weak.

If every constructed example satisfies the theorem, the examples may be biased by the same definition.

Include a near-miss example that the definition must reject.

The author must not choose only examples generated by its own constructors.

## Apply the theorem-survival test

Replace the intended definition with a plainly weaker substitute.

Then inspect the theorem.

If the proof still works, the theorem does not characterize the intended mathematics.

Replace the construction with an arbitrary object equipped with the desired isomorphism.

If naturality or classification still follows, the proof concerns transport data rather than the named construction.

Replace substantive morphisms with maps defined by conjugation through the target comparison.

If the theorem becomes automatic, it proves the transport choice, not the underlying mathematics.

This test does not require the author to recognize its own bias. It changes the object and observes what survives.

## Apply the unfolding test

Unfold every local definition used by the theorem.

Then write the theorem in ordinary mathematical language.

If the result becomes one of these forms, classify it as weak:

```text
Given a witness of P, prove P.
Given an isomorphism to X, prove an isomorphism to X.
Given a map defined to commute, prove that it commutes.
Given a complete classification, prove that the classification is complete.
Given an object defined by invariant I, prove that it has invariant I.
```

The theorem can remain as an interface lemma. It cannot support a claim of mathematical completion.

## Require a comparison theorem

A new representation of a standard object must connect to the established object.

Use one of these comparisons:

- definitional equality;
- proved equality;
- equivalence;
- categorical equivalence;
- comparison functor;
- forgetful map with characterized image;
- universal-property equivalence;
- an `if and only if` theorem under explicit hypotheses.

State which comparison applies.

Do not say two constructions “correspond” without defining the comparison.

Do not use matching names as evidence of matching semantics.

Do not export a new construction under a standard name before proving the comparison.

When no formal reference exists, compare against the source’s defining properties and distinguishing examples.

## Make authorities carry real force

A source must be allowed to falsify the implementation.

If the source definition disagrees with the Lean definition, change the Lean definition.

Do not reinterpret the source until it matches the code.

Do not replace the source with a later paper that uses more convenient conventions without reporting the change.

Do not cite a characterization while omitting its hypotheses.

Do not turn a theorem valid under extra hypotheses into the general definition.

Do not treat one computational criterion as the mathematical object unless the authority does so.

Record whether each sourced statement is:

- a definition;
- an equivalent characterization;
- a sufficient condition;
- a necessary condition;
- a classification theorem;
- a computational criterion;
- an example.

These roles are not interchangeable.

## Protect difficult proof obligations

A missing proof is not permission to edit the statement until it closes.

Keep the original theorem visible when:

- the standard definition makes the proof difficult;
- Mathlib lacks a needed bridge;
- the source uses undeveloped prerequisite theory;
- the correct categorical home remains unclear;
- a comparison theorem is not yet available;
- the theorem might need stronger hypotheses.

State the exact open obligation.

A visible gap preserves the research programme.

A circular definition hides the gap and corrupts later work.

## Distinguish representation lemmas from mathematical theorems

Use accurate labels.

Examples include:

```text
constructor_projection
transported_map_commutes
comparison_hom_naturality
underlying_object_iso
representation_sanity
```

These names identify implementation facts.

Reserve mathematical theorem names for results derived from independent definitions and hypotheses.

Do not name a transported fact after the source theorem it imitates.

Do not let namespace placement upgrade a representation lemma into mathematics.

## Require semantic content in naturality

Naturality can express a real theorem. It can also confirm a map engineered to commute.

Before defining a functorial action, define the mathematical action independently.

Then state why the comparison square commutes.

The proof should use facts about the construction.

Examples include:

- maps preserve primary submodules;
- localization commutes with the relevant operation;
- pullback satisfies its universal property;
- restriction preserves the form;
- sums commute with the underlying linear map.

If the proof uses only the comparison isomorphisms that defined the action, naturality has no independent content.

Call the result transported naturality.

Do not call it functoriality of the original mathematical construction.

## Require one positive and one separating example

A grounded formalization needs two different examples.

The positive example shows that the intended object satisfies the definition.

The separating example distinguishes the definition from a plausible weaker substitute.

For example:

- one exact sequence and one sequence with only zero composite;
- one nondegenerate form and one form with trivial-looking coordinates but nonzero radical;
- one true product and one object with projection maps but no universal property;
- one primary decomposition and one arbitrary direct-sum presentation;
- one invariant classification and one pair sharing the invariant without being equivalent.

A positive example alone cannot distinguish the intended definition from a weak one.

## Use the deletion question

For every theorem, ask:

> If I delete the local definitions, what independent mathematical fact remains?

If nothing remains, the result describes only the local encoding.

For every definition, ask:

> Which source statement forces this exact data and these exact axioms?

If no source or project decision answers, the definition lacks grounding.

For every comparison, ask:

> Could I have made this theorem true by changing the map definition?

If yes, define the map independently before accepting the comparison.

## Stop self-confirmation after the first weak theorem

One weak theorem can be an interface lemma.

A sequence of weak theorems indicates a self-sealing theory.

Observable signals include:

- several proofs close by `rfl`;
- several theorems project structure fields;
- naturality follows from conjugation definitions;
- every example uses local constructors;
- no counterexample tests the boundary;
- no theorem imports an external mathematical result;
- definitions become stronger whenever proofs fail;
- theorem statements become weaker whenever definitions resist;
- citations appear only after implementation;
- the same author supplies every semantic comparison.

When any two signals occur, stop adding declarations.

Return to the external definition and rebuild the dependency direction.

Do not ask whether the current theory “feels mathematically sound.” The author’s judgment is already inside the failed loop.

## Final grounding rule

No internally generated proof can establish that its own definitions represent a standard mathematical concept.

That claim requires an external anchor and an explicit comparison.

The formal kernel certifies:

> This conclusion follows from these declarations.

It does not certify:

> These declarations formalize the mathematical object named in their comments.

The second claim remains the author’s responsibility. The author must discharge it through sources, comparisons, and separating examples.

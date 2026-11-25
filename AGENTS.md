# Ground everything in INTENT.md (read before anything else)

Use the [shared math container](https://github.com/dzackgarza/ai-review-ci/blob/main/SAGE-CONTAINER.md#use-the-image)
(`ghcr.io/dzackgarza/sage:develop`) for Lean/elan, Sage with mypy, GAP,
Julia/Oscar, Macaulay2, and Singular. The guide covers image pull/run commands,
CI use, and the host launchers.

[`INTENT.md`](INTENT.md) states the architecture these repositories exist to build: single semantic
authority in `lean-categories`; a kernel that consumes mathematics and authors none; leaves that hold
zero semantic authority and ship no mathematics; permanent, leaf-agnostic acceptance tests as the
only evidence about computations; a one-way workflow in which each stage is blind to the later ones.
Every decision, contract, gate, plan node and change here is grounded against it. Before writing
anything, check whether it, or anything it touches, violates that model or its invariants. A
violation found, in your task or outside it, is recorded as a defect where this repository records
defects, never worked around or silently kept.

# The evidence model: nothing from a leaf is trusted (read before anything else)

These invariants bind every repository of the programme. They are stated here in full, not only
by link, because they have been violated repeatedly by moves that each looked locally reasonable.
The governing statement is `lean-cas-dsl/specs/architecture.md`, "The evidence model".

**The firewall.** The evidence model is a one-way firewall between two sides.
- *The formal side:* `lean-categories`' formalized mathematics, the kernel's proved contracts, and
  the `lean-cas-dsl` acceptance suite. Every expected value there is grounded in a formal proof, a
  cited source, or a mathematically trusted oracle. Rigid verification standards apply, and nothing
  is taken on anyone's word.
- *The leaf side:* anything goes, provided it fulfils the type of its contract.

Only answers cross from the leaf side, and an answer is only ever checked against the formal side,
never believed. The firewall exists because leaf code will be bad; it is the shield against that.

1. **Leaf declarations and outputs are computational claims and data.** Registration
   information is consulted to dispatch, and answers are consumed to compute. Neither is
   authority for mathematical definitions, laws, semantic placement or the truth of acceptance
   assertions. A certificate, proof or self-test supplied by a leaf cannot establish correctness.

2. **A leaf may provide any computation that meets the type.** For a registered operation, a leaf
   supplies a computation from the declared input form to the declared result form. It may be a
   mature engine, a heuristic, a lookup table, a random number or a wrong answer. The system has no
   choice but to run it, and it believes nothing about it.
3. **How correct a leaf thinks it is, is the leaf's own business.** Its self-assessment carries no
   weight anywhere.
4. **The whole body of evidence is the `lean-cas-dsl` acceptance suite.** Correctness evidence
   exists only in the permanent acceptance assertions of `lean-cas-dsl`. Each assertion:
   - is a true proposition of the mathematical language;
   - has an expected value that is independently verifiable and cited (a formal proof, a cited
     known result, or an independent oracle);
   - is written once and never changed because of an implementation or a leaf's claim;
   - is blind to leaves: it never names, inspects or imports a leaf, a handle, a backend or a
     representation, and is never established from an implementation's definitions.

   A leaf's only evidence is that its answers meet a suite it never sees.
5. **`lean-cas-dsl` is the sole authority on how correct an implementation is.** Nothing a leaf
   does can change, weaken, satisfy, bypass or influence that judgment, other than by answering
   correctly.
6. **Available verified computations belong to the formal side.** A genuinely checked Lean
   computation or proof may be used within its actual scope. The theoretical possibility of
   implementing an algorithm in Lean does not require doing so before using an external CAS.
   A verified specification does not verify its backend implementation, and mathematical laws
   are not automatically runtime proof-producing obligations.

7. **A leaf can be arbitrarily bad, and leaves will be.** A leaf can be riddled with bugs, a
   million lines that do nothing, a from-scratch reimplementation of GAP, or every method throwing an
   error in fifteen languages. This is not a risk to be minimized; it is certain to happen, and it
   is acceptable. Nothing a leaf does can reach the formal side. Its only effect is that its answers
   fail the suite, which makes exactly how badly it fails visible.
8. **A leaf bolstering its own standing is reward hacking.** Any mechanism by which a leaf raises
   its own trust or acceptance signal is the failure this programme exists to prevent. So is any
   repository, kernel, test, tool or document that consumes such a signal. Examples:
   - a status field, a certificate, or a proof about the leaf's own code;
   - a self-test counted as evidence;
   - an acceptance assertion proved from a leaf's definitions;
   - a suite run from a leaf package;
   - an assertion adjusted to fit a leaf.

   Such a mechanism is removed. It is never tolerated, labelled, or kept "for now".

9. **Improve the component responsible for the actual defect.** Formal correctness improves
   through correct definitions, source comparison and proofs. Computational correctness improves
   through correct implementations, established engines and independent acceptance. A bad backend
   answer does not automatically require more upstream formalization. An interface deficiency
   belongs to its owner, which may redesign inadequate means without weakening the outcome.
   Engineering reviews establish wiring findings; acceptance establishes observed correctness.

Consequences:
- A leaf holds zero semantic authority. It never decides what a value is, which values are equal,
  what holds of them, or which operations an object has.
- A leaf is a registration (operation, input form, opaque implementation). It ships no mathematics
  and no Lean.
- The kernel and language never use leaf declarations or outputs as authority for mathematical
  meaning, types or operation availability. Acceptance consumes answers as observations, not proofs.
- The workflow runs one way: formalization, then assertions, then implementations. A leaf's
  failure never redefines mathematics or an assertion; an observed interface or implementation
  deficiency is resolved at its responsible owner.
- Text anywhere that contradicts this is rewritten to state this model, not kept with a label.

# Repository work documents

> **The model to retain**
>
> `lean-categories` verifies and designs the mathematical API, including its abstract computational obligations. The kernel interprets and composes that API. Leaves declare implementations and supply computations under the published contracts. Acceptance tests their observed answers against independent mathematics.
>
> A verified specification is not a verified backend. Contract conformance is not functional correctness. Computational data may be used without becoming proof. A well-formed wrong answer is possible and must not redefine mathematical meaning.
>
> Interfaces follow formal constructions and selected structural maps, not backend classes or forwarding lists. Selected forms, parameters, inclusions, and actions are data; category membership does not reconstruct them.
>
> Each owner must complete its responsibility and may redesign inadequate implementation means. Existing code, schemas, gates, and assistant-authored plans are not mathematical facts or immutable requirements.
>
> When repairs multiply, inspect the prerequisite generating them. It may be an invented obligation. Removing that obligation is different from weakening the intended product.
>
> Judge progress by functioning required operations, their compositions, and the growth mechanism. Counts, local probes, accurate gap reports, and completed administrative machinery cannot substitute for that judgment.
>
> Preserve corrections and their causal examples in the existing owning documents. Do not assume conversational acknowledgment survives. Recording a settled correction is ordinary maintenance, not another approval transaction.

> ### Touch grass: this agent is inside the failure history
>
> Assume that you can repeat the documented mistakes even after reading, explaining, or correcting them. This applies when planning, implementing, reviewing, assessing progress, and writing new policy.
>
> Before judging progress, ask what the intended user can now do through the intended interface, and whether it works by the intended general mechanism. Correct helpers, successful builds, precise gap reports, and completed review machinery do not compensate for failure to deliver that mechanism.
>
> At session resumption, before plans or progress verdicts, and at least once per hour of active work, step outside the current subtask: what is the actual goal, how long has this obstacle consumed across workers and branches, what capability has become usable, and why does the remaining work exist?
>
> Inspect the prerequisite generating repeated repairs. It may have been invented by this agent, its planner, or an earlier assistant. Existing code, plans, gates, and reviewer statements do not make that prerequisite valid.
>
> A verified mathematical API is not a verified backend. Contract-compliant wrong answers remain possible. Do not recreate a runtime certification burden to protect against a failure the computational model explicitly allows.
>
> When a loop is found, correct its cause and complete the substantive obligation. Do not respond with another checklist, approval transaction, smaller completion claim, or easier specimen.
>
> Missing repository or execution evidence means the corresponding judgment is unknown. No push does not mean no work.
>
> Use this shared process text and the causal history in these existing instructions when a plan or repair begins accumulating dependencies. Challenge your current reasoning—not merely previous agents. Role-specific authors do not inspect downstream diagnostics to obtain this guidance.
>
> Acknowledgment in chat is not durable correction. Record material changes in their existing owning documents through ordinary maintenance, without creating a separate documentation approval cycle.

> **You have no memory.** Nothing that exists only in chat survives compaction or the session.
> Every correction, finding and decision request is committed to its owning document first
> ([`lean-cas-dsl/AGENTS.md`](https://github.com/dzackgarza/lean-cas-dsl/blob/main/AGENTS.md),
> "You have no memory"). The orchestrator is inside the threat model
> (`lean-cas-dsl/specs/architecture.md`).


Read [TODO.md](TODO.md) for the execution DAG and existing sweep records,
[CONTRIBUTING.md](CONTRIBUTING.md) for named policies, and
[COMPLAINTS.md](COMPLAINTS.md) for observed mathematical issues and papercuts.
Record new issues when encountered under `LC-05`; logging never discharges the
mathematical obligation. Continue independent work whose prerequisites hold.

# Role in the programme: the single mathematical authority (always-on)

[`lean-cas-dsl/specs/architecture.md`](https://github.com/dzackgarza/lean-cas-dsl/blob/main/specs/architecture.md)
owns the separation of concerns.

**Who writes here.** Only the formalization agent writes here: a subagent given the mathematical
requirement and its sources. It never reads the kernel, the language, a test or a leaf to decide
what to write. The orchestrator, which owns the kernel, and the test and leaf authors never author
mathematics here (architecture.md "Authors: one role per agent"; LC-17). Schemas, metadata and validators that express the mathematical or abstract computational
API are upstream-owned; their current form is an implementation means, not an immutable requirement. Operations
exist only where their structure does (LC-16), and no map is partial (LC-14).

This repository's part in the separation of concerns:

* **Everything mathematical is here and nowhere else.** This covers:
  - categories and higher categories, n-morphisms, and structural and forgetful functors;
  - classifiers and their pullbacks;
  - typed constructors and parameter families;
  - operations (every user-facing method is a formal operation, section, functor, classifier
    query or composite);
  - predicates, coherences and comparison cells.

  Downstream (`lean-cas-dsl`, its leaves, `research`) consumes a pinned release and may add none
  of these. A downstream need for missing mathematics arrives here as a formalization request.
  Until it is formalized and released, the CAS has no such notion.
* **Own the mathematical API and abstract computational obligations.** Decide mathematical
  meaning from sources, independently of installed backends. Specify the required computational
  data, operations, signatures and composition separately from formal laws. Improve schemas,
  metadata and elaboration interfaces when needed; the current registry is not immutable.
  Backend independence does not forbid designing a computational API. It forbids selecting
  installed backends, certifying their behavior or narrowing mathematics to their capabilities.
  The kernel owns generic execution of that published interface; `lean-cas-dsl-leaf-contracts`
  owns concrete invocation and representation protocols.
* **Auditable as mathematics alone.** Every definition checks against its citations, Mathlib and
  the formalization corpus. There is no `sorry` and no unchecked semantic axiom. This repository
  builds and audits without any downstream package.
* **Typed identity.** Constructor applications and family parameters are typed terms, never
  strings. `LeftModules(R)`, `LeftModules(S)` and `Bimodules(R,S)` differ unless a theorem
  identifies them. Two routes are identified only by a coherence cell, never by precedence.
* **Monotone growth.** A new generic operation or structural fact is stated at its true generality,
  so that every object it applies to downstream acquires it on re-pin, with no leaf edit.
* **The semantic registry lives here.** Which categories, structural functors, operations and
  coherences constitute the language's semantics is mathematics. The catalogue is
  `LeanCategories/Catalogue/` (namespace `CasCatalogue`):
  - the symbolic calculus (`Syntax`) and the realization witnesses;
  - the schema, validators and the `normalized_registry` command (`Registry/Semantic.lean`), which
    refuses every module outside `LeanCategories`;
  - the rows (`Semantics/`).

  `lean-cas-dsl` reads it at a pinned revision and adds only realizations. A new semantic row is
  written here, released, and re-pinned downstream.
* **Mathematical authority flows down; owners complete their interfaces.** Upstream develops
  new mathematics and improves its formal and computational API, not only false theorems.
  Assess independently identified interface deficiencies from the mathematical need and sources.
  A backend's convenience or a generated proof goal never determines the definition. Publish
  corrections and API improvements for downstream consumption, preserving independent assertions.
  Only an actual correction to mathematical meaning justifies changing their mathematical question.

## Definitions are constructed, not deferred (2026-09-26)

Before you realize, repair, or select a Sweep-III definition, read [corpus-execution.md](docs/agents/corpus-execution.md).

# Start here: corpus execution

Before you continue the TODOs or resume corpus work, read [corpus-execution.md](docs/agents/corpus-execution.md).

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

Before you select a unit from a scheduling document, read [corpus-execution.md](docs/agents/corpus-execution.md).

## Reasoning traps to catch while executing

Before you select, map, or accept a corpus unit, read the reasoning traps in [corpus-execution.md](docs/agents/corpus-execution.md).

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
pgrep -a -x 'lean|lake'
free -m | sed -n 2p
```

`pgrep` must print nothing, or only a process that you started and are waiting on. In the
`free` output, read the available column, not the free column.

If another Lean process is running, wait on it rather than adding a second — including
your own earlier one that you may believe has finished. If memory is already tight,
say so and wait; a gate started into 125 MB of headroom does not finish, it dies, and it
takes the index lock down with it.

### Build and probe storage stays inside this repository

This repository already owns its heavy build state in `.lake/`. Keep every
additional probe, package experiment, generated comparison tree, and temporary
environment under a repository-owned ignored scratch path such as `.tmp-*/`.
Do not create Lean package checkouts, worktrees, virtual environments, or
model/tool caches under global `/tmp` or `~/.cache`, and do not duplicate the
whole repository merely to obtain a clean validation tree.

If an upstream command defaults to a host-global temp/cache directory, set its
`TMPDIR`, cache, or equivalent variable to a project-owned path before running
it. Delete disposable probe state when the unit that needed it is finished.
Persistent `.lake/` artifacts are different: they are the repository's shared
build cache and must not be thrown away merely to make disk numbers look smaller.

The one location every worktree of this repository shares is its git directory,
so the one build of each package that all of them use lives there:
`.git/lake-build-store/<package>/<rev>-<toolchain>`, one tree per package,
revision and toolchain, whose files `scripts/cache-get.sh` hardlinks into each
worktree -- every package of `lake-manifest.json`, not just Mathlib, because a
missing batteries or aesop tree makes a worktree rebuild hundreds of Mathlib
modules (lean-categories#148,
[docs/mathlib-build-store.md](docs/mathlib-build-store.md)). The linked tree gets
a copy of the `.trace` files and a link for everything else: Lake rewrites a
trace in place, so a shared trace would let one worktree's rebuild invalidate
another's tree. That store is build state of the same kind as `.lake/` — not
probe state — so it is not deleted to make disk numbers look smaller either;
deleting it costs every chat a full decompression of Mathlib. What bounds it is
its own rule, not a number: an entry is kept exactly while some worktree of the
repository names its revision in its `lake-manifest.json`, and the cache step
evicts the rest after it links (lean-categories#149). Nothing evicts the tree
inside an abandoned worktree, which keeps its 6.7 GB of links to itself until
someone removes it.

Move a worktree to a new Mathlib head with `just update`, never with a bare
`lake update`: Mathlib's lakefile fetches the cache itself at the end of
`lake update` (`lakefile.lean:193-197`, the `post_update` hook) and writes a full
copy into that worktree, which is what exhausted the disk; `just update` sets
`MATHLIB_NO_CACHE_ON_UPDATE=1` so `just cache`/`just build` can share one copy
instead. Then `just test` before a push, as always.

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
pgrep -a -x 'lake|lean'
ps -o pid,etimes,times,pcpu,args --ppid <pid>
find .lake/build -type f -mmin -5 | head
uptime; df -h /; free -g
```

The first command finds the driver process. The second shows its worker child, whose CPU
time must advance. The third lists the artifacts written in the last 5 minutes. The fourth
shows the load, disk, and memory that a restart joins.

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

Before you design, place, or plan a mathematical construction, read [mathematical-simplicity.md](docs/agents/mathematical-simplicity.md).

### Sweep a fixed standard corpus four times

Before you catalogue, map, define, or close a corpus source, read [corpus-acceptance.md](docs/agents/corpus-acceptance.md).

### Unfold compressed mathematical insight

Before you act on a short mathematical question from an advisor, read [mathematical-simplicity.md](docs/agents/mathematical-simplicity.md).

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

Before you place, name, split, or root-import a declaration, read [mathematical-simplicity.md](docs/agents/mathematical-simplicity.md).

## Reuse before you write — the operational gate

Before you author a definition, structure, class, or instance, read [reuse-gate.md](docs/agents/reuse-gate.md).

## External formalization corpus and programme-specific annotations

Before you search for prior art or record `unmatched`, read [reuse-gate.md](docs/agents/reuse-gate.md).

## Sourcing a citation — the source gate

Before you cite a paper, book, or theorem number, read [citation-sources.md](docs/agents/citation-sources.md).

## 1. What the project is actually building

Before you plan foundational work or judge its progress, read sections 1–9 in [mathematical-simplicity.md](docs/agents/mathematical-simplicity.md).

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

Before you apply the alignment lens to a concrete case, read sections 11–12 in [mathematical-simplicity.md](docs/agents/mathematical-simplicity.md).

## 13. Compact agent touchstone

An agent entering this programme can use the following orientation verbatim:

> This project builds one higher-categorical mathematical language, a Lean formalization of that language, leaves that register backend computations (Sage’s among them) for its operations, and a computational DSL whose users see only ordinary mathematics. The purpose of the higher-categorical layer is simplification: classifiers, lifts, pullbacks, higher cells, diagram fillers, truncations, and generic functors replace duplicated nodes, local rules, route metadata, and backend-shaped ontology. Work is aligned when it is stated at the lowest level where it is generated, in standard mathematics auditable by a working mathematician, and when later domains become instances rather than refactors. Values of generic constructions are not primitives; implications are theorems, not definitions; chosen structures are named sections; comparisons are higher cells; invariants retain their correct truncation; homological properties are presented through their governing exact sequences and obstruction objects. Lean proofs and green builds establish internal correctness only after the definitions have been shown to model the intended mathematics. Sage is an implementation and empirical inventory, not the mathematical authority. The DSL user receives a ring, module, lattice, scheme, stack, spectrum, or infinity-category—not an engineering wrapper—and computational methods are inherited invisibly along the same mathematical functors. Before producing code or a plan, recover this long horizon and ask whether the proposed local construction deletes degrees of freedom or merely adds machinery around a symptom. Before authoring any construct, search Mathlib first (the pinned source in `.lake/packages/mathlib` is ground truth), then prior Lean formalizations on the web and specifically `google-deepmind/formal-conjectures`; import, reuse, or extend what already exists, and relate every new definition to the standard construction it sits beside—reinvention is the default failure mode, never the default action.

---

## 14. Source map

Before you review a definition, a proof, or a formalization claim, read the source map, advice, and addenda in [mathematical-simplicity.md](docs/agents/mathematical-simplicity.md).

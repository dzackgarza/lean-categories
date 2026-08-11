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

### Treat compilation as a structural check

A successful build proves that all imported declarations typecheck together.
It does not prove unique ownership, semantic agreement, or correct categorical placement.

Before adding a foundation to the root surface, identify its exact category and functors.
Also identify its predicates, universal properties, and relationship to existing foundations.

---

## Reuse before you write — the operational gate

Sections 4.3–4.4 and 10.2 give the *principle* (novelty bias, false gaps, mathematical home); this is the *procedure*, and it is a hard gate. **Do not author a new definition, structure, class, or instance until you have searched for an existing one, and if you still write your own, related it to what exists.** The measure of good foundational work is accidental freedom removed (§0); the cheapest way to remove it is to not re-derive what Mathlib or a prior formalization already owns. Minimal reinvention, maximal integration-compatibility with Mathlib, is the standing default — reinvention is the failure mode, never the first move.

Before writing any construct, in order:

1. **Search Mathlib first — it is the default home.** The repo pins Mathlib in `.lake/packages/mathlib`; that tree is ground truth for the exact version we build against. Search it directly (`rg` the source) and via Loogle / LeanSearch / the Mathlib docs before concluding anything is missing. **Prefer Mathlib's formulation whenever it is at least as general** (ledger #1 ruling) — do not fork a narrower parallel definition.
   - A missing *exact name* is not a missing construction (§4.4). Standard mathematics is usually a composition of what Mathlib already has: categories of elements, comma/slice categories, full subcategories, pullbacks, cores, sections, equivalences, adjunctions, essential images. Build from those.
   - Every work-unit issue carries a verified **"Mathlib reuse"** comment (reuse / extend / genuinely-absent, each with `Namespace.Decl` + file path, checked against the pinned version). That is your starting inventory: reuse the "reuse" tier directly, extend the "extend" tier, and only the "genuinely-absent" tier is new authorship. Keep those comments current as Mathlib moves.

2. **Then search prior formalizations on the web.** If Mathlib lacks it, check whether it has been formalized elsewhere *before* writing your own: Lean-community projects on GitHub, in-flight Mathlib PRs, and other proof-assistant developments. When a reference implementation exists, **use it** — import if it is packaged and licensed, otherwise port/adapt it and cite the source — rather than reinventing.
   - **Search [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures) specifically.** It holds Lean formalizations of many statements and constructions this programme touches. When it has a relevant one, **import, reuse, or rewrite/extend it** — do not restate it from scratch. It is also the sanctioned home for genuinely-unproved deep statements (conjecture ledger, issue #21).

3. **Only then write new — and relate it to what exists.** A new construct with no stated relationship to a standard one is a red flag (§4.1, §4.4). Every new definition must, in the same PR, carry its tie to the existing world: an equivalence, comparison functor, or forgetful/instance relationship to the Mathlib **or in-repo** construction it specializes, generalizes, or sits beside. Build for **integration compatibility** — reuse Mathlib's typeclasses, category conventions, and morphism classes so the result composes with the library instead of shadowing it. (An equivalence to a standard object does not by itself legitimize a bespoke parallel hierarchy — §4.6 — but its *absence* is worse: the new object then floats free of the mathematics it claims to model.)

4. **Record the search.** When you do write new, state what you searched and why the existing pieces did not suffice — in the PR, and in the owning issue if the fact is durable. "Not found in Mathlib / formal-conjectures / a reference project" is a negative finding: report the searched scope, never "does not exist." A later agent must be able to see the reuse gate was actually run.

The failure this gate prevents is §4.3 and §4.4: writing a plausible new definition is faster and *feels* more productive than finding the three-line composition of existing constructions that already says it. That is not progress — it is a new maintenance surface and an avoidable comparison theorem later.

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

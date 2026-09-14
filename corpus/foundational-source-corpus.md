---
type: reference
title: Foundational source corpus
description: '# Foundational source corpus'
tags:
- project
- reference
timestamp: '2026-09-07T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# Foundational source corpus

# Foundational source corpus

# Foundational source corpus v1

## Status

**Corpus v1 is frozen.** It is the fixed denominator for the first four foundational sweeps. Changing membership, edition, or bounded scope requires an explicit corpus-version amendment; downstream work may not silently add a book, chapter, or local prerequisite.

**Amendment v3 is in force.** Amendment v2 admitted `FC13`–`FC16` without renumbering, re-editioning or rescoping `FC01`–`FC12`. Amendment v3 admits Kerodon as `FC17` without changing any existing source-unit ID. See "Corpus v2 amendment" and "Corpus v3 amendment" below.

The corpus order is fixed before cataloguing. It is a chosen topological order of the mathematical prerequisite graph, with **abstraction ownership** included in the dependency relation: a later source may be mathematically readable without an earlier source, but if its formalization should reuse an earlier generic object/category/functor rather than invent a local one, the generic source comes first.

## Frozen corpus v1 order

| ID     | Source                                                                                                             | Pinned version/scope                                                                           | Depends on                             | Prerequisite reason                                                                                                                                                                                                                                           |
| ------ | ------------------------------------------------------------------------------------------------------------------ | ---------------------------------------------------------------------------------------------- | -------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `FC01` | Dummit–Foote, *Abstract Algebra*                                                                                   | 3rd ed., Wiley, 2004; complete book, excluding exercises by default                            | —                                      | Base algebraic language: sets/functions as used in the text, groups, rings, modules, fields, tensor constructions, linear algebra, Galois and representation vocabulary. In particular modules exist before module localization or homological constructions. |
| `FC02` | Munkres, *Topology*                                                                                                | 2nd ed., Prentice Hall, 2000; complete book, excluding exercises                               | —                                      | General topological language before sheaves on spaces, algebraic topology, or manifolds. Independent of most algebra, but fixed second so later topology-bearing sources have one owner.                                                                      |
| `FC03` | Riehl, *Category Theory in Context*                                                                                | Dover, 2016; complete book, excluding exercises                                                | `FC01` (examples/structured hosts)     | Ordinary categories, functors, natural transformations, limits/colimits, adjunctions, representability, monads and Kan extensions before later algebraic constructions are given categorical owners.                                                          |
| `FC04` | Atiyah–Macdonald, *Introduction to Commutative Algebra*                                                            | Addison–Wesley, 1969; complete book, excluding exercises                                       | `FC01`, `FC03`                         | Depends on rings/modules from `FC01`; `FC03` is required by the project’s categorical realization order so localization/change-of-rings constructions receive functorial owners rather than later wrappers.                                                   |
| `FC05` | Weibel, *An Introduction to Homological Algebra*                                                                   | Cambridge Studies in Advanced Mathematics 38, 1994; complete book, excluding exercises         | `FC01`, `FC03`, `FC04`                 | Generic complexes, exactness, resolutions, derived functors, Ext/Tor and spectral sequences after modules and ordinary category theory, before topology and algebraic geometry instantiate them.                                                              |
| `FC06` | Hartshorne, *Algebraic Geometry*                                                                                   | GTM 52, Springer, 1977; local 2008 printing; complete Chapters I–V, exercises excluded         | `FC01`–`FC05`                          | Schemes, sheaves, cohomology, divisors, curves and surfaces after commutative/local algebra, topology, category theory and generic homological algebra.                                                                                                       |
| `FC07` | Hatcher, *Algebraic Topology*                                                                                      | Cambridge Univ. Press, 2002; complete book, excluding exercises                                | `FC01`, `FC02`, `FC05`                 | Algebraic topology depends on topology/algebra; generic chain/homological objects should already have owners from `FC05`.                                                                                                                                     |
| `FC08` | Lee, *Introduction to Smooth Manifolds*                                                                            | 2nd ed., GTM 218, Springer, 2013; complete book, excluding exercises                           | `FC01`, `FC02`, `FC07`                 | Smooth manifolds after point-set topology; differential forms/de Rham constructions should reuse the preceding algebraic-topological substrate rather than define isolated copies.                                                                            |
| `FC09` | Neukirch, *Algebraic Number Theory*                                                                                | Grundlehren 322, Springer, 1999 English ed.; complete book, excluding exercises                | `FC01`, `FC04`                         | Arithmetic branch after rings/modules and commutative algebra; supplies number rings, valuations, completions, ramification, adeles/ideles and class groups used by arithmetic lattice work.                                                                  |
| `FC10` | Serre, *Local Fields*                                                                                              | GTM 67, Springer, 1979 English ed.; complete book, excluding exercises                         | `FC01`, `FC04`, `FC09`                 | Owns complete discretely valued/local-field and ramification vocabulary before p-adic lattice theory.                                                                                                                                                         |
| `FC11` | Peters–Sterk, *Symmetric and Quadratic Forms, with Applications to Coding Theory, Algebraic Geometry and Topology* | June 2024 version present locally; complete text, excluding exercises                          | `FC01`, `FC04`, `FC09`, `FC10`         | Forms/lattices after modules, commutative algebra and the local arithmetic needed for p-adic lattices/genus; primary project forms source.                                                                                                                    |
| `FC12` | Beauville, *Complex Algebraic Surfaces*                                                                            | 2nd ed., LMS Student Texts 34, Cambridge Univ. Press, 1996; complete book, excluding exercises | `FC05`, `FC06`, `FC07`, `FC08`, `FC11` | Surface layer after scheme/sheaf/divisor theory, topology/smooth geometry, homological tools, and the forms/lattice language used by the project.                                                                                                             |

## Corpus v2 amendment

Four sources are admitted as corpus members. Each closes a gap in the v1 dependency spine; none is admitted for subject breadth.

| ID     | Source                                                              | Pinned version/scope                                                                            | Depends on                     | Prerequisite reason                                                                                                                                                                                                                                                          |
| ------ | ------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------- | ------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `FC13` | Matsumura, *Commutative Ring Theory*                                | Cambridge Studies in Advanced Mathematics 8; trans. M. Reid; complete book, excluding exercises | `FC01`, `FC04`, `FC05`         | Owns the homological commutative algebra Atiyah–Macdonald omits and Hartshorne assumes: regular sequences and depth, Cohen–Macaulay and regular local rings, Koszul complexes, completion, dimension theory and flatness criteria. Traversed after `FC05` and before `FC06`. |
| `FC14` | Humphreys, *Introduction to Lie Algebras and Representation Theory* | GTM 9, Springer; complete book, excluding exercises                                             | `FC01`, `FC03`                 | Owns semisimple Lie algebras, root systems, Weyl groups, weights and finite-dimensional representation theory. No v1 source defines a root system.                                                                                                                           |
| `FC15` | Humphreys, *Reflection Groups and Coxeter Groups*                   | Cambridge Studies in Advanced Mathematics 29; complete book, excluding exercises                | `FC01`, `FC11`, `FC14`         | Owns finite and affine reflection groups, Coxeter systems, geometric representations and root data. The project's reflection/orbit applications use these as primitives; `FC11` supplies the form-theoretic ambient.                                                         |
| `FC16` | Humphreys, *Linear Algebraic Groups*                                | GTM 21, Springer; complete book, excluding exercises                                            | `FC01`, `FC04`, `FC06`, `FC14` | Owns linear algebraic groups, their actions, Borel/parabolic structure and root data over a base, so group actions on varieties/schemes reuse one owner rather than local stand-ins.                                                                                         |

`FC13` is a prerequisite of `FC06`, so numeric ID order is no longer the traversal order. Corpus v2 traverses:

`FC01`, `FC02`, `FC03`, `FC04`, `FC05`, `FC13`, `FC06`, `FC07`, `FC08`, `FC09`, `FC10`, `FC11`, `FC12`, `FC14`, `FC15`, `FC16`.

Amendment v2 also admits Folland, *Real Analysis: Modern Techniques and Their Applications*, and Conway, *A Course in Functional Analysis*, as **supplementary only**. No corpus source's dependency spine passes through measure theory or functional analysis, so neither enters the sweep denominator.

## Corpus v3 amendment

Kerodon is admitted as a full corpus source rather than a supplementary catalogue.
It is an online, growing reference, so this amendment pins the exact repository-owned
metadata snapshot instead of pretending that a mutable website is an editioned book.

| ID | Source | Pinned version/scope | Depends on | Prerequisite reason |
| --- | --- | --- | --- | --- |
| `FC17` | Jacob Lurie, *Kerodon* | `corpus/kerodon-source-units.json`, retrieved `2026-09-14T13:34:50Z`; every non-structural stable tag in that snapshot, including the retired part and exercises | `FC01`, `FC02`, `FC03`, `FC05`, `FC07` | Owns the higher/homotopy-coherent category-theory branch: simplicial sets, ∞-categories/quasicategories, fibrations, Kan-extension/cofinality machinery, and related constructions. Its definitions must pass through the same ecosystem Mapping gate as every other admitted source rather than becoming an isolated reference list. |

Corpus v3 traverses the v2 order unchanged and then `FC17`:

`FC01`, `FC02`, `FC03`, `FC04`, `FC05`, `FC13`, `FC06`, `FC07`, `FC08`, `FC09`, `FC10`, `FC11`, `FC12`, `FC14`, `FC15`, `FC16`, `FC17`.

The canonical Sweep-I catalogue is
`corpus/foundational-corpus-units-fc17-kerodon.md`, generated from the normalized
snapshot by `scripts/index_kerodon.py`. Kerodon's permanent tag is the source
identity; the generated `FC17-KER-Uxxxxx` ID is a deterministic encoding of that
tag and therefore does not change when the live text moves the item. The exact
statement remains authoritative at `https://kerodon.net/tag/<TAG>` and
`https://kerodon.net/data/tag/<TAG>/content/statement`; Sweep II reads that source
statement before accepting a mapping. Refreshing the snapshot does **not** silently
expand this amendment: a changed stable-tag population is a corpus-scope change and
requires another explicit amendment.

## Local Markdown extraction manifest

All frozen corpus-v1 sources already have full-book Markdown extractions available locally. Sweep I uses these exact files as its primary traversal inputs; the source/edition table above remains authoritative if extraction metadata and filenames disagree.

| ID     | Markdown extraction                                                                                                                                       | Verification                                              |
| ------ | --------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------- |
| `FC01` | `/home/dzack/Zotero/storage/XIINH8MK/local-write-api-1783380265761-A4FFDNKB_extracted.md`                                                                 | Full extraction through page 947; reaches terminal index. |
| `FC02` | `/home/dzack/Zotero/storage/CZQDCAJR/local-write-api-1783249491889-EEDYK7RG_extracted.md`                                                                 | Full extraction through page 552; reaches terminal index. |
| `FC03` | `/home/dzack/Zotero/storage/NQXEU8HD/local-write-api-1783451282930-TIDLVIT4_extracted.md`                                                                 | Full extraction through page 258; reaches terminal index. |
| `FC04` | `/home/dzack/Zotero/storage/JCFIJ7EH/local-write-api-1783448143508-XL7FDEDH_extracted.md`                                                                 | Full extraction; reaches terminal index.                  |
| `FC05` | `/home/dzack/Zotero/storage/SI35IEE3/Weibel - 1994 - An Introduction to Homological Algebra.md`                                                           | Full extraction; reaches terminal index.                  |
| `FC06` | `/home/dzack/Zotero/storage/AMY5NQZM/[Hartshorne 2008] Algebraic geometry.md`                                                                             | Full extraction; reaches terminal index.                  |
| `FC07` | `/home/dzack/Zotero/storage/QDLM25QY/Hatcher - 2002 - Algebraic Topology.md`                                                                              | Full extraction; reaches terminal index.                  |
| `FC08` | `/home/dzack/Zotero/storage/HSU4DVYA/local-write-api-1783416009444-PW4NSUST_extracted.md`                                                                 | Full extraction through page 723; reaches terminal index. |
| `FC09` | `/home/dzack/Zotero/storage/BSXFFMGF/local-write-api-1783468319638-8698XMKC_extracted.md`                                                                 | Full extraction through page 583; reaches terminal index. |
| `FC10` | `/home/dzack/Zotero/storage/CWP929L4/Serre - 1979 - Local Fields.md`                                                                                      | Full extraction; reaches terminal index.                  |
| `FC11` | `/home/dzack/Zotero/storage/ANG3AN65/[Peters 2024] Symmetric and Quadratic Forms, with Applications to Coding Theory, Algebraic Geometry and Topology.md` | Full extraction; reaches terminal index.                  |
| `FC12` | `/home/dzack/Zotero/storage/W2IAU2UK/Beauville - 1996 - Complex Algebraic Surfaces.md`                                                                    | Full extraction; reaches terminal index.                  |

No Sweep-I source-acquisition task is presently required for FC01–FC12. If one of these files proves corrupt or incomplete during traversal, repair/re-extract that same pinned source; do not substitute another edition or silently change corpus scope.

The four v2 sources have local PDFs but **no** Markdown extraction. Each requires a Sweep-I source-acquisition task — extract the pinned PDF and verify the extraction reaches a terminal index — before it can be catalogued.

| ID     | Source PDF                                                                                                                            | Extraction status                                                                                                                                                                        |
| ------ | ------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `FC13` | `/home/dzack/Zotero/storage/JHZDICNF/local-write-api-1781955283942-TSA7KUJB_matsumura.pdf`                                            | Extracted to `/home/dzack/Zotero/storage/JHZDICNF/Matsumura - Commutative Ring Theory.md`; 329 PDF pages; reaches terminal index.                                                        |
| `FC14` | `/home/dzack/Zotero/storage/Z435A56I/Introduction to Lie Algebras and Represent - J.E. Humphreys.pdf`                                 | Extracted to `/home/dzack/Zotero/storage/Z435A56I/Humphreys - Introduction to Lie Algebras and Representation Theory.md`; 186 PDF pages; reaches terminal GTM-series list after indexes. |
| `FC15` | `/home/dzack/Zotero/storage/7QPFIKHI/James E. Humphreys - Reflection groups and Coxeter groups-Cambridge University Press (1997).pdf` | Extracted to `/home/dzack/Zotero/storage/7QPFIKHI/Humphreys - Reflection Groups and Coxeter Groups.md`; 216 PDF pages; reaches terminal index.                                           |
| `FC16` | `/home/dzack/Zotero/storage/782SZTXW/Linear Algebraic Groups - James E. Humphreys.pdf` | Extracted to `/home/dzack/Zotero/storage/782SZTXW/Humphreys - Linear Algebraic Groups.md`; 276 PDF pages; OCR-derived from the pinned image-only PDF; reaches terminal indexes and GTM-series list. |

The two supplementary admissions are also local PDFs only: Folland at `/home/dzack/Zotero/storage/HFDC2XPA/Real Analysis Modern Techniques and Their - Gerald B. Folland.pdf` and Conway at `/home/dzack/Zotero/storage/QVLZ5UJP/A Course in Functional Analysis - John B. Conway.pdf`. Neither is a sweep input.

`FC17` is source-acquired through Kerodon's public stable-tag hierarchy rather than a
local PDF extraction. The pinned normalized snapshot contains 8,189 unique stable
tags, of which 7,673 are non-structural mathematical units. The generated catalogue
is the Sweep-I input; no copied statement/proof prose is required because each unit
retains its permanent authoritative Kerodon tag and statement endpoint.

The table is a deterministic traversal order. The source-unit catalogue additionally records fine-grained dependencies between individual units, so independent material inside a later book need not falsely depend on every earlier theorem.

## Why this order

The ordering is intentionally not alphabetical or “one book per subject.” The dependency spine is the point. Examples:

- `Module` from `FC01` precedes localization and local module theory in `FC04`.
- Categories/functors from `FC03` precede categorical realization of localization, base change, sheaf operations, derived functors, and the project DSL's structural functors.
- Generic complexes/derived functors from `FC05` precede Hatcher/Hartshorne instances, avoiding separate topology-specific or scheme-specific homological foundations.
- Point-set topology from `FC02` precedes sheaves/topological constructions, Hatcher, and Lee.
- Hartshorne precedes Beauville so curves/surfaces are an extension of the scheme/sheaf/divisor theory rather than a parallel surface ontology.
- Neukirch/Serre precede Peters–Sterk's local arithmetic layer so p-adic lattice notions use the existing arithmetic vocabulary.

## Supplementary sources

Existing catalogues for Folland, Ahlfors, Shafarevich, Whitehead, Apostol, Lam, Gerstein, Milnor–Husemöller, and other references remain valuable and are not discarded. They are supplementary unless a corpus version explicitly admits them. Supplementary formalization work remains valid but does not alter the sweep denominator.

Amendment v2 adds Conway, *A Course in Functional Analysis*, to this supplementary list, and confirms Folland's *Real Analysis* as supplementary rather than a corpus member. Measure theory and functional analysis are a deliberate exclusion, not an oversight: no corpus source's dependency spine passes through them.

The entire Stacks Project is deliberately **not** an implicit corpus member. If a later corpus version needs a bounded deformation/stack source, its exact chapters/tags or another finite standard source must be admitted explicitly before that version is catalogued.

## Four sequential sweeps over one corpus

The same stable source-unit IDs feed four separate plans:

1. **Catalogue sweep:** inventory every formal mathematical unit in source order.
2. **Lean-ecosystem mapping sweep:** for every unit, exhaustively search existing Lean work and decide the canonical reuse/import/reference/unmatched route. No new mathematics is authored.
3. **Definition sweep:** implement or port only the definitional residue not already supplied by an accepted route, at the correct categorical owner.
4. **Theorem sweep:** formalize only the remaining non-definitional residue after definitions exist.

The mapping sweep is intentionally separate from cataloguing. Corpus membership and source content must be known before implementation availability is investigated; otherwise search results distort what gets catalogued.

## Sweep-I unit schema

Every unit records:

- stable source-unit ID (`FCxx` + source-local unit ID);
- source/version, chapter/section, exact definition/theorem/page location;
- kind: definition, construction, convention, notation, lemma, proposition, theorem, corollary, named example, comparison, or another explicitly named formal kind;
- concise mathematical data/statement with exact hypotheses;
- dependencies on earlier source units needed to state it.

Implementation ownership/status is **not** required to catalogue a unit. Any known route may be recorded provisionally, but Sweep II owns the systematic search.

## Sweep-II mapping schema and search order

Every source-unit ID receives one mapping record. Search is exhaustive over known formalization work, not limited to Lean or to a hand-picked repository registry.

Search order:

1. the pinned `.lake/packages/mathlib/Mathlib` source, by declaration/type shape and standard synonyms;
2. current `leanprover-community/mathlib4`, including source history and relevant open PRs;
3. the live [`formalization-corpus`](https://github.com/dzackgarza/formalization-corpus) index: use the [browser](https://dzackgarza.github.io/formalization-corpus/) and, for systematic mapping, `scripts/formalization_corpus.py` or a client generated from the [OpenAPI reference](https://dzackgarza.github.io/formalization-corpus/api.html); the live OpenAPI document is authoritative for API paths, methods, and schemas. Search source names, standard synonyms, theorem names, expected declarations/type fragments, and nearby constructions rather than one literal phrase;
4. Loogle, LeanSearch, Mathlib docs, and the local source atlas;
5. Lean Reservoir and every packaged Lean dependency/repository it exposes;
6. GitHub code/repository search across **all discoverable Lean repositories**, especially revision history, open work, or repositories not yet present in the hosted corpus;
7. Rocq, Agda, Isabelle, and other proof-assistant repositories indexed by `formalization-corpus`, when they provide a checked reference implementation;
8. locally mirrored/vendored Lean reference corpora and statement banks such as `formal-conjectures` where relevant.

The hosted corpus is a discovery index over current snapshots, not commit-pinned mapping evidence. After a hit, inspect the actual upstream declaration and record repository/package, commit/tag, path, declaration name, license, toolchain/Mathlib compatibility, and mathematical comparison. Its [`SOURCES.md`](https://github.com/dzackgarza/formalization-corpus/blob/main/SOURCES.md) is the canonical evolving registry of indexed projects; do not maintain a competing repository inventory here. If the hosted API is unavailable, that outage does not count as a negative search and cannot justify `unmatched`.

For each candidate, inspect the actual declaration and hypotheses; name similarity is not a match. Record repository/package, commit/tag, path, declaration name, license, toolchain/Mathlib compatibility, and mathematical comparison to the corpus unit.

Each unit ends in exactly one route class:

- `mathlib`: use the canonical pinned Mathlib declaration/proof directly;
- `project-existing`: an existing canonical LeanCategories declaration already owns it;
- `package-import`: an external Lean package can be imported as a dependency;
- `reference-port`: a checked implementation exists but is not directly importable, including implementations in another proof assistant; preserve exact provenance and port/adapt from that reference rather than rederive it;
- `unmatched`: no acceptable implementation source was found after the exhaustive search.

Only `unmatched` definitional units are slated for genuinely new mathematical formalization. `reference-port` units are port/integration work, not greenfield mathematics. Mapping failures are scoped negative findings tied to the search date and corpus unit, never claims that no formalization exists anywhere forever.

## Sweep-III definition boundary

The definition sweep consumes Sweep II's routes. Mathlib/project/import routes require no new mathematical definition; reference-port routes are ported/adapted with provenance; only `unmatched` units receive new Lean authorship. All definitions are placed at the lowest correct mathematical/categorical owner, defining missing ambient categories and structural functors when necessary.

Proofs intrinsic to well-definedness remain part of definition realization: category/functor laws, independence of representatives, closure, quotient well-definedness, etc. General source lemmas/theorems do not.

## Sweep-IV theorem boundary

After Sweep III, traverse every non-definitional unit. Reuse the mapping from Sweep II first; prove only the unmatched theorem residue. Difficult proofs may remain open for a long time and do not narrow the completed definitional DSL. A consumer is blocked only by the exact theorem units it actually requires.

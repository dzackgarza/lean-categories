# Active mathematical work

## Execution DAG

The nodes below reference the full sweep obligations in this file. `Needs`
lists immediate prerequisites; an entry `A` on node `B` means `A -> B`.
These edges express the existing sweep order, not new completion claims.
The linked whole-source ledger remains the sole source of sweep completion.

| ID | Obligation | Needs |
| --- | --- | --- |
| `corpus` | [Admitted sources, editions, scope and source acquisition](#0-foundational-corpus-and-in-force-amendments) | none |
| `catalogue` | [Sweep I: every source unit](#1-sweep-i--catalogue-every-corpus-unit) | `corpus` |
| `mapping` | [Sweep II: map every unit onto an existing formalization where one exists](#2-sweep-ii--map-every-unit-onto-existing-formalizations). Bulk candidate discovery is corpus-wide; semantic adjudication remains source-ordered. | `catalogue` |
| `definition-mapping-convergence` | **MILESTONE 1 / STATE TRANSITION.** State 1 is complete: every definitional mapping is semantically verified, systematic second-pass search has converged, and the final unconstrained open-ended prior-art search found no further viable implementation/reference for the surviving residue. This node performs no search itself; it is the gate from “minimize the definitional work” to “do the minimized definitional work.” | `definition-open-ended-prior-art-search` |
| `definitions` | [Sweep III: definitions and intrinsic laws](#3-sweep-iii--realize-the-complete-definitional-layer) | `definition-mapping-convergence` |
| `definition-realization-convergence` | **MILESTONE 2 / TERMINAL DEFINITION STATE.** State 2 is complete: every definitional unit is realized and source-faithful. Reused, imported, ported, and newly authored definitions collectively realize every clause of the original prose reference, with intrinsic well-definedness/structure laws discharged and the final source-conformance audit complete. This node performs no implementation itself; it certifies convergence of State 2. | `definition-source-conformance` |

The definition rows below deliberately carry no counts. They used to, and every one of them was
wrong within the day: `fc05-definitions` still read "199 pending of 376" after the source had
closed at 371 of 371, and the denominator had moved twice under classifier repairs. A count
copied into this file is a second, frozen copy of something the frontier regenerates, and a
worker reading the stale copy either redoes closed work or stops short of the real remainder.
Read the frontier. `unmatched` is not a forecast of how much mathematics this repository should
invent. The cheap discovery pass is the corpus-wide `FOUNDATIONAL_DEFINITIONS.tsv` worklist plus its
generated candidate census; run that pass in bulk for all sources. Semantic acceptance of candidates
and the bounded first-stage negative-search pass are then discharged source-by-source. After the last
source-local mapping pass, systematic second-pass search works the residue in source/topic batches;
then `definition-open-ended-prior-art-search` performs the final unconstrained search for anything
the structured passes missed. Milestone 1 closes only after that final task reaches a fixed point,
and **no** Sweep-III authoring begins before the gate. Do not serialize API retrieval
behind source order, and do not block this definitional milestone on mapping unrelated
theorem/remark/example rows.


| `track-the-catalogue` | **Completed 2026-09-13.** The 378 Markdown records formerly reachable only through the private `.agents/references/` symlink are now tracked under `corpus/`: source catalogues, per-unit mappings, provenance contracts, the source atlas, source manifest, and whole-source ledger. `scripts/foundational_frontier.py` defaults to that tracked directory, and a fresh clone with no `.agents` or `.hermes` symlink regenerates `FOUNDATIONAL_FRONTIER.md` byte-for-byte. `.agents`, `.hermes`, and the known local probe scripts are explicitly ignored as scratch/private automation. **Acceptance:** every catalogue and mapping file is tracked, `git log` shows them, and a fresh clone regenerates `FOUNDATIONAL_FRONTIER.md` identically | none |
| `retire-the-stale-catalogue-copy` | **Completed 2026-09-13.** Before deletion, the superior committed vault versions of `chapter-1-varieties-fc06.md`, `provenance-contract-for-fc06-c01.md`, and `index.md` were ported byte-for-byte into tracked `corpus/` and `FOUNDATIONAL_FRONTIER.md` regenerated from them. The vault commit `2965de28` then deleted the project `references/` subtree (378 files), leaving `corpus/` as the sole writable catalogue/mapping source. The `.agents` symlink intentionally remains because private `plans/` and `decisions/` still live behind it; `.agents/references` no longer exists and must not be recreated. **Acceptance:** `corpus/` is authoritative for all catalogue/mapping records; `.agents/references` is absent; `.agents/plans` and `.agents/decisions` remain live | `track-the-catalogue` |
| `mapping-record-coverage` | **Completed for FC01–FC16 on 2026-09-13; FC17 was admitted later.** The original sources have parsed mapping rows for their catalogue units. FC17's 7,673 units were added by the v3 amendment and deliberately do not retroactively make that historical claim false. Its 861 definitional rows are handled by `definition-discovery`/`fc17-mapping`; its non-definitional rows remain Sweep-II obligations before Sweep IV. | `track-the-catalogue` |
| `definition-discovery` | **Completed 2026-09-15.** Build the corpus-wide definitional retrieval surface before serial semantic mapping work. `python scripts/foundational_definition_index.py` must generate one row for every Sweep-III definition/construction/notation/convention, joining source data, current route and mapping hint; `python scripts/foundational_definition_candidates.py` must search every `action=search` row through the OpenAPI-resolved `formalization-corpus` batch operation with resumable checkpoints. This is cheap candidate discovery, not semantic acceptance and not the final residue audit: hits still require source-clause comparison and zero hits do not authorize invention. **Acceptance:** the generated definition table has the exact frontier denominator and every search row has a completed candidate-census entry or an explicit transport failure to repair. | `catalogue`, `mapping-record-coverage` |
| `audit-authored-definitions` | **Separate from Mapping.** After Milestone 1 closes, review locally authored definitions when the verified mapping shows that an external owner already supplies the mathematics. Replace genuine reinvention with the checked owner or record the mathematical reason the external implementation cannot serve. This is realization cleanup, not Mapping evidence. | `definition-mapping-convergence` |
| `fc05-mapping` | **Completed after provenance correction.** Reopened the stale negative definition routes for live discovery and re-adjudicated them through the OpenAPI corpus plus targeted source inspection. Mapping routes are causal: implementations landed after the reopen do not rewrite their own provenance. FC05 now has 368/368 definition mappings accepted: 229 `mathlib`, 86 `project-existing`, 1 `package-import`, 5 `reference-port`, and 47 scoped `unmatched [negative-search-complete]`; the complete 1,059-unit FC05 catalogue retains a canonical mapping row for every unit. | `definition-discovery` |
| `fc13-mapping` | **Completed 2026-09-15.** Every FC13 definitional row has completed source-clause semantic adjudication. Positive rows route to direct reuse or pinned reference ports; every surviving unmatched row carries `[negative-search-complete]` and is provisional residue for the later systematic/open-ended audits. No first-pass `search` or `review` row remains. | `fc05-mapping`, `definition-discovery` |
| `fc06-mapping` | **Completed 2026-09-15.** Every FC06 definitional row has completed source-clause semantic adjudication against the current catalogue. Chapters I–III were rechecked in source order; Chapter IV had its stale pre-reparse unit-ID drift repaired before adjudication; Chapter V received a fresh four-cluster live-corpus pass. Positive rows route to direct reuse or pinned reference ports, and every surviving unmatched row carries `[negative-search-complete]` as provisional residue. No first-pass `search` or `review` row remains. | `fc13-mapping`, `definition-discovery` |
| `fc07-mapping` | **Completed 2026-09-15.** Every FC07 definitional row has completed source-clause semantic adjudication against the current Hatcher catalogue. The refreshed pass recovered direct Mathlib owners for retractions, the inductive CW-complex construction, coherent/compactly-generated topology and domination; accepted cross-prover/reference ports include sphere-map degree (Cubical Agda), Koszul graded commutativity (Atlas), and ENR theory (Isabelle/HOL). Strong but non-source-general prior art such as LeanPool Whitehead machinery and Cubical Gysin is recorded without over-routing it. Every surviving unmatched row carries source-local `[negative-search-complete]` evidence and is provisional State-1 residue; no first-pass `search` or `review` row remains. | `fc06-mapping`, `definition-discovery` |
| `fc08-mapping` | **Completed 2026-09-15.** Every FC08 definitional row has completed source-clause semantic adjudication against the current Lee catalogue and expanded 886-source formalization corpus. The final pass recovered direct/native routes for mechanics terminology and predicates, an OpenGA reference port for the metric musical isomorphism, and Atlas prior art for the Poisson-bracket formula; it also preserved exact source-model distinctions where Lee’s point-derivation cotangent bundle lacks a checked smooth equivalence to Mathlib’s native tangent-Hom bundle. Every surviving unmatched row carries source-local `[negative-search-complete]` evidence and is provisional State-1 residue; no first-pass `search` or `review` row remains. | `fc07-mapping` |
| `fc09-mapping` | **Completed 2026-09-15.** Every FC09 definitional row has completed source-clause semantic adjudication against the Neukirch catalogue and current expanded formalization corpus. The pass recovered landed TauCeti routes for function-field divisor theory, higher-unit/lower-ramification infrastructure and ideal Artin maps; Atlas supplies compatible ray-class prior art, while admitted Atlas/TauCetiRoadmap targets were retained only as evidence. Source paragraphs were split rigorously between their actual definition/predicate and later theorem consequences, eliminating many false definition gaps in class-field, character and conductor sections. Every surviving unmatched row carries source-local `[negative-search-complete]` evidence and is provisional State-1 residue; no first-pass `search` or `review` row remains. | `fc08-mapping` |
| `fc10-mapping` | **Completed 2026-09-15.** Every FC10 definitional row has completed source-clause semantic adjudication against the Serre *Local Fields* catalogue and the current expanded formalization corpus. The pass separated actual definitions from theorem consequences throughout ramification, Tate/Galois cohomology, class formations and local-symbol chapters; this removed many false definition gaps while preserving genuine residues such as the truncated-Witt ring scheme, nonabelian `H¹` pointed quotient/connectors, Brauer quotient group/functor structure, and general ell-adic curve/Jacobian representations. Every surviving unmatched row carries source-local `[negative-search-complete]` evidence and is provisional State-1 residue; no first-pass `search` or `review` row remains. | `fc09-mapping` |
| `fc11-mapping` | **Completed 2026-09-16.** Every FC11 definitional row has completed source-clause semantic adjudication against the Peters--Sterk catalogue and current formalization corpus. The canonical index has 387/387 accepted first-pass mappings: 231 `mathlib`, 79 `project-existing`, 31 `reference-port`, and 46 scoped `unmatched [negative-search-complete]`; no first-pass `search` or `review` row remains. The surviving 46 rows are provisional residue for `fc11-definition-residue-pass2`/the later open-ended audit, not authorization for Sweep III. | `fc10-mapping` |
| `fc12-mapping` | **Completed 2026-09-15.** Every FC12 definitional row has completed source-clause semantic adjudication against Beauville and the current expanded formalization corpus. The canonical index has 45/45 accepted first-pass mappings: 1 `mathlib`, 4 `project-existing`, and 40 scoped `unmatched [negative-search-complete]`; no first-pass `search` or `review` row remains. The surviving 40 rows are provisional residue for `fc12-definition-residue-pass2` and the later open-ended audit, not authorization for Sweep III. | `fc11-mapping` |
| `fc14-mapping` | **Completed 2026-09-16.** Every FC14 definitional row has completed source-clause semantic adjudication. The canonical index has 176/176 accepted first-pass mappings: 104 `mathlib`, 43 `reference-port`, and 29 scoped `unmatched [negative-search-complete]`; no first-pass `search` or `review` row remains. The final Chapter-VII pass recovered direct native routes for the module weight lattice, the stabilizer lattice of an admissible lattice, and its integral dual/contragredient carrier. The surviving 29 rows are provisional residue for the later second/open-ended searches, not authorization for Sweep III. | `fc12-mapping` |
| `fc15-mapping` | **Completed 2026-09-16.** Every FC15 definitional row has completed source-clause semantic adjudication. The canonical definition index has 122/122 accepted first-pass mappings: 100 `mathlib`, 3 `reference-port`, and 19 scoped `unmatched [negative-search-complete]`; no first-pass `search` or `review` row remains. The pass recovered direct native routes across finite/affine/abstract Coxeter theory, invariant theory, Bruhat/cell carriers, and Schur-multiplier data, while preserving exact Atlas generic-Hecke operator prior art and isolating only source-general construction/comparison residue. | `fc14-mapping` |
| `fc16-mapping` | **Completed 2026-09-16.** Every FC16 definitional row has completed source-clause first-pass semantic adjudication against Humphreys and the current formalization corpus. The current canonical index has 162/162 accepted mappings: 113 `mathlib`, 42 `reference-port`, and 7 scoped `unmatched [negative-search-complete]`; no first-pass `search` or `review` row remains. Some later structured residue evidence was recorded prematurely and is tracked separately below; it does not alter the fact that this first-pass node is closed. | `fc15-mapping` |
| `fc17-mapping` | **Completed 2026-09-16.** Every one of the 861 FC17 definitional units has completed permanent-tag source-clause first-pass semantic adjudication against the current formalization corpus and inspected candidate/reference evidence. The canonical definition index has 861/861 accepted first-pass mappings: 814 `mathlib`, 2 `reference-port`, and 45 scoped `unmatched [negative-search-complete]`; no first-pass `search` or `review` row remains. The 45 unmatched rows are provisional residue for `fc17-definition-residue-pass2` and the later open-ended audit, not authorization for Sweep III. Mapping the remaining 6,812 theorem/remark/example/equation units remains Sweep-II work before Sweep IV and does not enter this definitional milestone. | `fc16-mapping`, `definition-discovery` |
| `definition-positive-route-audit` | **Verify every positive definitional Mapping claim before Milestone 1.** Traverse the positive-route population from the canonical definition index. Reuse an existing comparison when it already records the complete source/declaration match; otherwise read the prose statement and actual declaration(s), verify every clause and the claimed generality, and repair false/partial/name-only routes. Exact repository/revision/path/declaration provenance must be present for external owners. This node is an audit of existing evidence, not an instruction to manufacture a new marker on already-good rows. **Acceptance:** no positive definitional route remains whose canonical row fails to demonstrate the complete source match. | `fc17-mapping` |
| `fc01-definition-residue-pass2` | **Completed 2026-09-16.** Re-ran the 18-row FC01 provisional definitional residue in source/topic batches with broader terminology, current pinned source inspection, and live formalization-corpus searches. The pass corrected nine false negatives to genuine pre-existing project owners (finite-abelian type/elementary-divisor/conversion data, holomorph, hypercenter/hypernilpotence, solvable length, subgroup-incidence geometry, incidence automorphisms, and squarefree part). Nine rows survive as scoped `unmatched [negative-search-complete]` residue for the later open-ended audit; mixed construction/theorem rows were routed definition-only so theorem obligations remain open. | `fc17-mapping` |
| `fc02-definition-residue-pass2` | **Completed 2026-09-16.** Regenerated the canonical definition index after FC01 pass2 and verified that FC02 has zero unmatched definitional rows; no synthetic search work or marker churn was manufactured. | `fc17-mapping` |
| `fc03-definition-residue-pass2` | **Completed 2026-09-16.** Re-ran all 24 FC03 provisional definitional residues in category-theory/topology topic batches against current project owners, pinned Mathlib, Riehl-specific repositories, and the live Formalization Corpus. Nineteen false negatives were corrected to pre-Mapping project owners, including selected subcategories, walking constructions, essential discreteness, commutative diagrams, strict creation, smash/bipointed topology, affine/free-module monads, algebraic-theory models, Riehl pointwise Kan extensions, homotopical/deformation/point-set-derived structures, codensity monads, and the site-theoretic Grothendieck-topos definition. Five rows survive as scoped `unmatched [negative-search-complete]` residue: three editorial/terminology conventions, the initial/terminal representable characterization, and the full matrix/based/unbased finite-dimensional comparison. The strongest new external partial for the latter is `jwiegley/category-theory@27f68f1089eb627188794f0c3d4df9ae32048529::Instance/FdVect.v`, which proves the matrix↔based equivalence but not the source's complete distinct three-category chain. | `fc17-mapping` |
| `fc04-definition-residue-pass2` | **Completed 2026-09-16.** Re-adjudicated all three FC04 provisional definitional residues against their mixed source clauses. C05-U031 now routes only the valid partial-homomorphism graph/extension-poset construction to the checked FLT reference while retaining the Lean-checked counterexample to the source's unconditional maximal-existence claim; C09-U013 routes the number-ring definition to pinned Mathlib while leaving the Gaussian-integer identification as comparison content; C11-U001 is recognized as graded/homogeneous setup over native carriers, with the missing graded Hilbert-basis implication retained at its separate theorem prerequisite. The regenerated index has zero FC04 unmatched definitional rows; no false theorem claim was discharged. | `fc17-mapping` |
| `fc05-definition-residue-pass2` | **Completed 2026-09-16.** Re-ran all 47 older FC05 `[negative-search-complete]` definitional residues in source/topic batches across pinned/current Mathlib, the live Formalization Corpus, first-pass candidate repositories, and declaration-style synonym searches. New hits were adjudicated clause-wise: Atlas's Alexander–Whitney/Eilenberg–Zilber work is singular-chain-specific and still contains `sorry`; Mathlib Lie cochains explicitly leave the CE-complex/central-extension layer TODO; category-theory comonad files mention but do not formalize the cotriple bar resolution; current cyclic/DG hits are wrong-carrier Hopf work or roadmap/sorry files; right-derived-functor infrastructure does not supply Weibel's RHom complex; and stable-spectrum hits do not realize the spectrification/cylinder/cone package. No exact route survived adjudication, so the 47 rows remain provisional `unmatched [negative-search-complete]` residue for the later open-ended audit. No definition authoring occurred. | `fc17-mapping` |
| `fc06-definition-residue-pass2` | **Completed 2026-09-16.** Re-ran all 75 FC06 provisional definitional residues in chapter/topic batches across pinned/current Mathlib and current external algebraic-geometry work. Important new partials were adjudicated rather than accepted by name: Atlas has a `sorry`-free Rees–Proj blowup/proper-transform construction but no checked comparison to Hartshorne's explicit affine-incidence blowup; its Cartier-divisor scheme is integral-scheme-only; its Proj twisting-sheaf layer depends on `sorry` definitions; ring-level differential code does not supply Hartshorne's scheme sheaf; and Mathlib's checked `SmoothOfRelativeDimension` lacks a checked equivalence to Hartshorne's exact flat/component-dimension/differential-rank predicate. Formal-scheme, absolute-Frobenius, Picard/Jacobian, Kodaira, and abstract hyperelliptic searches produced no source-complete checked route. All 75 rows therefore remain provisional `unmatched [negative-search-complete]` residue for the final open-ended audit; no definition authoring occurred. | `fc17-mapping` |
| `fc07-definition-residue-pass2` | **Completed 2026-09-16.** Re-ran the 51 FC07 provisional definitional residues in topology/algebraic-topology topic batches against git provenance, pinned/current Mathlib, and the live cross-prover corpus. Two false negatives were corrected to genuine pre-Mapping project owners: the based smash quotient (`Topology/SmashProduct.lean@393c451`) and, definition-only, the reduced-suspension quotient (`Homological/Prespectrum.lean@a312c92`), leaving its comparison with unreduced suspension for theorem work. New source-shaped partials were adjudicated without over-routing: Cubical Agda now supplies a genuine cofiber/cup-square Hopf invariant but only in its target-dimension-at-least-two parameterization; its Gysin package remains stronger-hypothesis prior art; Atlas cap/cross-product declarations or dependencies contain `sorry`; and transfer/local-coefficient/Steenrod declaration searches produced no checked source-general owner. The regenerated residue therefore drops by two; all survivors remain provisional `[negative-search-complete]` for the later open-ended audit. No definition authoring occurred. | `fc17-mapping` |
| `fc08-definition-residue-pass2` | **Completed 2026-09-16.** Re-ran all 87 FC08 provisional definitional residues in manifold/differential-geometry topic batches. Fourteen mixed rows were corrected to definition-only native reuse because the definition itself was already a literal predicate over checked primitives (topological immersion/submersion, regular values/defining maps, weak embedding, boundary defining functions, regular domains/sublevel sets, faithful representations, space-filling terminology, parallelizability, equilibria, exact one-forms, and Riemannian completeness/boundedness); their bundled theorem/example clauses remain open. Current Mathlib's Riemannian-distance layer justified the completeness split, while orientation/integration/density, exterior calculus/de Rham, arbitrary submanifold tangency, symplectic/contact/Hamiltonian/jet and related carriers remain source-incomplete. TauCeti's checked smooth two-form/nondegeneracy layer explicitly lacks closedness, so it was retained only as partial evidence. Timed-out searches were rerun individually. The regenerated FC08 residue is 73 rows, all provisional `residue-search`; no definition authoring occurred. | `fc17-mapping` |
| `fc09-definition-residue-pass2` | **Completed 2026-09-17.** Re-ran all 38 FC09 provisional definitional residues in arithmetic topic batches against pinned/current Mathlib, project history, the live Formalization Corpus and current TauCeti/Atlas/KummerCriterion work. Strong candidates were re-adjudicated rather than accepted by name: Mathlib Henselianity is still simple-root rather than Neukirch factor lifting; exact factor-lifting/Herbrand APIs remain `sorry` roadmap targets; TauCeti relative discriminant lacks the checked equality to Neukirch's basis-generated presentation; ordinary group colimits do not supply topological-group inductive limits; current idèle infrastructure lacks the assembled global Galois action and Atlas's idèle norm still depends on admitted completion support; p-adic-log, Arakelov/metrized-`K_0`, formal-module, Weber and Borel-regulator searches produced no source-complete checked owner. No route survived the clause comparison, so all 38 rows remain provisional `unmatched [negative-search-complete]` for the final open-ended audit. No definition authoring occurred. | `fc17-mapping` |
| `fc10-definition-residue-pass2` | **Completed 2026-09-17.** Re-ran all seven FC10 provisional definitional residues against project history, pinned/current Mathlib, the live Formalization Corpus, importable packages and targeted current Lean searches. One false negative was corrected: `FC10-C10-U027` has an exact proof-complete `package-import` owner in pinned `Whysoserioushah/BrauerGroup@54a54e35`, which defines tensor-product multiplication on Brauer classes, the commutative-group structure, scalar-extension homomorphism and field-to-commutative-group functor. The other six rows survive as provisional `unmatched [negative-search-complete]`: the truncated Witt ring scheme, general ℓ-adic curve/Jacobian representation package, and four nonabelian group-`H¹`/connecting-map constructions. Mathlib's nonabelian `Sites` `H¹` is Čech/presheaf cohomology rather than Serre's group-action object, and Mathlib's group-cohomology file explicitly leaves nonabelian cohomology TODO; external hits were abelian-only or `sorry` roadmaps. No definition authoring occurred. | `fc17-mapping` |
| `fc11-definition-residue-pass2` | **Completed 2026-09-17 after prerequisite revalidation.** The early 2026-09-16 pass had already searched/adjudicated every then-current FC11 residue and recovered the lattice Nikulin involution `FC11-C20-U060`. After `fc17-mapping` closed, the pass was revalidated against the current canonical index: exactly the same 46 `residue-search` IDs survive, all 46 canonical mapping rows still carry scoped second-pass evidence, no FC11 mapping record changed after that pass, and `U060` remains a positive route. Fresh live-corpus searches across the surviving Brown/Milgram, K3/Kummer, plumbing/lens/Hirzebruch--Jung, Witt/semi-discriminant, Jacobian Weil-pairing, Milnor/Lefschetz, and Hodge/Néron--Severi clusters found no new source-complete owner. The 46 survivors remain provisional `[negative-search-complete]` residue for the final open-ended audit; no definition authoring occurred. | `fc17-mapping` |
| `fc12-definition-residue-pass2` | Same second-pass task for FC12. | `fc17-mapping` |
| `fc13-definition-residue-pass2` | Same second-pass task for FC13. | `fc17-mapping` |
| `fc14-definition-residue-pass2` | Same second-pass task for FC14. | `fc17-mapping` |
| `fc15-definition-residue-pass2` | Same second-pass task for FC15. | `fc17-mapping` |
| `fc16-definition-residue-pass2` | **Evidence was recorded early on 2026-09-16, but this node is not closed because its prerequisite `fc17-mapping` is still open.** The premature structured pass broadened searches over the then-current FC16 residue and semantically eliminated several false residues by respecting separately catalogued source prerequisites (including the Borel variety `G/B`, the rank-one reflection, `B(λ)`, and the anisotropic-kernel construction). The current canonical index has seven provisional FC16 residues. After `fc17-mapping` closes, revalidate this evidence against the then-current canonical index before closing the node; do not count the early pass as DAG completion. | `fc17-mapping` |
| `fc17-definition-residue-pass2` | Same second-pass task for FC17/Kerodon, beginning from permanent-tag terminology but searching equivalent and historically different names as well. | `fc17-mapping` |
| `definition-residue-pass2` | **Join for the systematic second-pass residue searches.** Source children may run independently. After they close, regenerate `FOUNDATIONAL_DEFINITIONS.tsv`; any newly positive route is semantically adjudicated and removed from residue, and any rows still lacking a completed first-stage mapping are sent back to the relevant `fcNN-mapping` node. This node does not certify final absence of prior art. | `fc01-definition-residue-pass2`, `fc02-definition-residue-pass2`, `fc03-definition-residue-pass2`, `fc04-definition-residue-pass2`, `fc05-definition-residue-pass2`, `fc06-definition-residue-pass2`, `fc07-definition-residue-pass2`, `fc08-definition-residue-pass2`, `fc09-definition-residue-pass2`, `fc10-definition-residue-pass2`, `fc11-definition-residue-pass2`, `fc12-definition-residue-pass2`, `fc13-definition-residue-pass2`, `fc14-definition-residue-pass2`, `fc15-definition-residue-pass2`, `fc16-definition-residue-pass2`, `fc17-definition-residue-pass2` |
| `definition-open-ended-prior-art-search` | **Final unconstrained State-1 search immediately before Milestone 1.** Take the complete residue surviving the structured mapping and second-pass DAG and task agents explicitly with finding *anything* that can avoid fresh definition work. Search beyond the known corpus/local engines without precommitting to repositories or query vocabularies: broad web/GitHub/repository discovery, author/project pages, papers and citations that point to code, current/open branches and PRs, histories, package ecosystems, theorem-prover communities, and newly discovered formalization projects. Follow plausible leads recursively and let one discovery generate new names/repositories/search directions for other residue rows. Record auditable evidence in the canonical mapping row: date, mathematical object, queries/search terms, surfaces, revisions where relevant, projects/repositories/branches/PRs inspected, candidates followed, and rejection reasons. Only survivors of this task receive `[residue-search-audited]`. If a viable reference is found, replace the negative route and continue searching the reduced residue. Regenerate the definition index and repeat until this task reaches a fixed point: no `action=search` or `action=residue-search` row remains and an unconstrained pass finds no new viable implementation/reference. | `definition-residue-pass2`, `definition-positive-route-audit` |
| `fc05-definitions` | Sweep III for FC05. Reuse/import/port accepted owners; author only rows that survived Milestone 1. Every port/new definition is checked against the complete original prose clauses and intrinsic laws before downstream use. | `definition-mapping-convergence`, `audit-authored-definitions` |
| `fc13-definitions` | Sweep III for FC13 under the same source-faithful realization rule. | `fc05-definitions` |
| `fc06-definitions` | Sweep III for FC06 under the same rule. | `fc13-definitions` |
| `fc07-definitions` | Sweep III for FC07 under the same rule. | `fc06-definitions` |
| `fc08-definitions` | Sweep III for FC08 under the same rule. | `fc07-definitions` |
| `fc09-definitions` | Sweep III for FC09 under the same rule. | `fc08-definitions` |
| `fc10-definitions` | Sweep III for FC10 under the same rule. | `fc09-definitions` |
| `fc11-definitions` | Sweep III for FC11 under the same rule. | `fc10-definitions` |
| `fc12-definitions` | Sweep III for FC12 under the same rule. | `fc11-definitions` |
| `fc14-definitions` | Sweep III for FC14 under the same rule. | `fc12-definitions` |
| `fc15-definitions` | Sweep III for FC15 under the same rule. | `fc14-definitions` |
| `fc16-definitions` | Sweep III for FC16 under the same rule. | `fc15-definitions` |
| `fc17-definitions` | Sweep III for the Kerodon definitional layer under the same rule. | `fc16-definitions` |
| `definition-source-conformance` | **Final corpus-wide definitional source audit.** Return to the original prose statement for every open-programme definition/construction/notation/convention and inspect the actual Lean realization (or reused owner plus specialization/comparison), not merely its name or mapping label. Verify all data, hypotheses, quantifiers, equations/coherences, variance, universe/generalization choices, quotient/representative conditions, and intrinsic construction laws. Check at least one intended and one separating/excluded example where meaningful. Repair any mismatch at its mathematical owner and revisit dependent realizations. **Acceptance:** no definitional row remains merely plausible/partial; every row has a usable realization whose complete mathematical content agrees with the source, and all source Definitions cells can be checked without relying on build success as semantic evidence. | `fc17-definitions` |
| `theorems` | [Sweep IV: remaining theorem obligations](#4-sweep-iv--formalize-the-remaining-lemmas-and-theorems) | `definitions`, and per source its own `fcNN-definitions` |
| `arithmetic-lattice-foundations` | Execute [PLAN-ARITHMETIC-LATTICE-FOUNDATIONS](.agents/plans/features/FEATURE-ARITHMETIC-LATTICE-FOUNDATIONS/plans/PLAN-ARITHMETIC-LATTICE-FOUNDATIONS/PLAN-ARITHMETIC-LATTICE-FOUNDATIONS.md) at its stated natural generality after the foundational source programme: projective formed modules, metric I-duality/modularity, Dedekind/projective arithmetic, equivariant lattices, height-one/local realizations, intrinsic local invariants, ring adeles and adelic genus, local classification, signature loci, and the exact comparison maps back to their Mathlib/project owners. Preserve every distinction the plan calls out: separation vs perfection, primitive vs finite-index embeddings, algebraic vs metric duality, integral ring adeles vs field adeles, and bilinear vs quadratic discriminant data. Reuse Mathlib and external owners before project implementation. **Acceptance:** the plan success criteria and phase/task consumers are realized with kernel-checked comparisons; no familiar special case silently replaces a parameterized construction | `theorems` |

| `refactor-audit` | Make one corpus-wide pass for duplicated Lean, parallel near-definitions, local restatements of existing corpus mathematics, and misplaced ownership, then repair each concrete defect at its actual owner while preserving the realized mathematics and public names unless the correction itself requires a change. Small and single-owner findings are repaired directly; create a separate DAG child only for a genuinely substantive cross-owner repair whose work cannot be completed coherently in this pass. Do not create report-, inventory-, approval-, or audit-receipt-only nodes. **Acceptance:** every concrete finding from the pass is repaired or has a precise unresolved mathematical/technical blocker, and a final read finds no remaining identified duplication or ownership defect. A no-finding pass closes this node without manufacturing work | `arithmetic-lattice-foundations` |
| `lint-paydown` | Pay down the linter obligations where reasonable and no further: mathlib's `#lint` suite, unused arguments, simp-normal-form, vacuity and axiom audits. Every change must improve the legibility of the statement, the ability to understand what it says, and the ability to check statically that it is the source's statement. Contorting a definition or proof only to quiet a linter is the failure mode; where it is genuinely warranted it must be judged as significantly serving that goal and the argument recorded explicitly in the commit message | `refactor-audit` |
| `bloat-audit-loop` | **Finite convergence pass, not a standing paperwork loop.** After `lint-paydown`, make one source-aware pass over reuse/reinvention, duplicate definitions and theorem statements, mathematical ownership, imports/namespaces, typeclass and universe design, proof size and idiomatic theorem use, `simp`/rewriting surfaces, test/lint proof integrity, axioms/vacuity, dead compatibility bridges, generated/static surfaces, and architecture/module cohesion. Search pinned/current Mathlib, open upstream work, Reservoir and discoverable Lean packages before improving a local mechanism that may be reinvention. Repair concrete findings at their owners with kernel-checked regressions; broad findings become explicit substantive DAG children only when they require real implementation work. **Acceptance:** every concrete finding from the pass is repaired or has a precise unresolved mathematical/technical blocker, and a final read finds no remaining identified defect. A no-finding pass closes this node with no receipt commit, complaint entry, dashboard, or recurring audit obligation. Later regressions are handled when observed rather than keeping this node permanently open. Do not weaken source statements or rewrite phase boundaries to make the pass green | `lint-paydown` |

Within a sweep, source dependencies and traversal order come from the existing
[source manifest](corpus/foundational-source-corpus.md); unit IDs and
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
directory. Those symlinks are private automation surfaces and are intentionally ignored by Git.
The durable mathematical corpus is different: source catalogues, mapping records, provenance
contracts, the source atlas, and the whole-source status ledger are tracked under `corpus/`.

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
[corpus status ledger](corpus/foundational-corpus-status.md) for the four sweeps
below. Reference material — source catalogues, mapping records, the Lean source atlas — lives in
the tracked `corpus/` directory. Changes to those records are ordinary repository changes and
must be committed with the work they describe; `.agents/` is never their canonical owner.

## The foundational programme

The foundational programme is source-based. Corpus v1 remains frozen, with the explicit v2 and
v3 amendments recorded in the source manifest. The exact editions or pinned snapshots,
source dependencies, prerequisite rationale, and verified source-acquisition paths live in
[the foundational source index](corpus/foundational-source-corpus.md). Whole-source
progress for all four sweeps lives only in the
[central corpus status ledger](corpus/foundational-corpus-status.md).

The same corpus is traversed in four separate sequential sweeps:

1. catalogue every mathematical unit;
2. map every unit against existing Lean formalizations;
3. realize the complete definitional layer;
4. formalize the remaining lemmas and theorems.

Do not merge these sweeps. In particular, implementation availability must not shrink the
catalogue, and theorem formalization may be long-running without holding the definitional DSL
hostage.

## 0. Foundational corpus and in-force amendments

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
version/amendment. Amendments v2 and v3 below are the only such changes so far. Existing
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

## 0b. Corpus v3 amendment — Kerodon

17. `FC17` Lurie, *Kerodon* (pinned stable-tag snapshot).

`FC17` is appended as the higher/homotopy-coherent category-theory branch. Its canonical
Sweep-I population is the pinned stable-tag snapshot under `corpus/`; definitions are not
allowed to bypass Sweep II merely because Kerodon is online. Its source-local Mapping and
Definitions nodes therefore follow `fc16-definitions` in the terminal definition programme.
Corpus v3 traverses the v2 order above and then `FC17`.

Two further sources are admitted as **supplementary only**, not as corpus members: Folland,
*Real Analysis: Modern Techniques and Their Applications*, and Conway, *A Course in Functional
Analysis*. No corpus source's dependency spine passes through measure theory or functional
analysis, so neither enters the denominator of the four sweeps. Supplementary formalization
against them stays valid.

All four v2 sources have local PDFs but no verified Markdown extraction. Each needs source
acquisition before Sweep I can traverse it.

## 1. Sweep I — catalogue every corpus unit

Plan: [PLAN-FOUNDATIONAL-CORPUS-CATALOGUE-SWEEP](.agents/plans/features/FEATURE-FOUNDATIONAL-CORPUS/plans/PLAN-FOUNDATIONAL-CORPUS-CATALOGUE-SWEEP/PLAN-FOUNDATIONAL-CORPUS-CATALOGUE-SWEEP.md).

Traverse every corpus source completely, in the v3 traversal order above. Record every formal
unit:

- definitions, constructions, conventions, and notation;
- lemmas, propositions, theorems, and corollaries;
- admitted named examples/comparison statements;
- exact source location, hypotheses/data, and source-unit dependencies.

- [x] Upgrade existing definition-only catalogues into complete source-unit catalogues.
- [x] Catalogue every source without consulting Lean coverage to decide whether a row belongs.
- [x] Assign stable source-unit IDs used unchanged by all later sweeps.

Which sources are catalogued is stated only in
[the corpus status ledger](corpus/foundational-corpus-status.md). The catalogues
themselves are one file per source in
`corpus/foundational-corpus-units-fc*.md`. Each catalogue is faithful to its frozen
Markdown extraction, which no phase has yet compared against the printed source.

A source is not fully catalogued merely because all of its definitions have existing Lean
routes; its theorem/lemma content still belongs to Sweep I.

## 2. Sweep II — map every unit onto existing formalizations

Plan: [PLAN-FOUNDATIONAL-CORPUS-MAPPING-SWEEP](.agents/plans/features/FEATURE-FOUNDATIONAL-CORPUS/plans/PLAN-FOUNDATIONAL-CORPUS-MAPPING-SWEEP/PLAN-FOUNDATIONAL-CORPUS-MAPPING-SWEEP.md).

FC01–FC16 received an initial row-coverage pass; FC17 was admitted later. Before further serial
adjudication, regenerate `FOUNDATIONAL_DEFINITIONS.tsv` and complete the bulk candidate census for
all unresolved definitional rows. Retrieval is intentionally corpus-wide: the API can answer many
independent searches in batches, and a candidate for FC16 is useful evidence even while FC05 is the
current implementation source. Do not recreate a one-query/one-row or one-source-at-a-time search
loop around an index designed for bulk retrieval.

After the candidate census, take a source, not a chapter, in v3 traversal order for semantic
adjudication. Compare candidates against each source statement and record positive routes with exact
provenance. A bounded mandatory-surface pass may mark a still-unresolved row
`[negative-search-complete]`, but that marker now means **provisional residue only**. It does not
authorize greenfield implementation.

After every source's definitional rows have undergone that semantic pass, State 1 continues through
two further layers. First run the source/topic-batched second-pass nodes, which revisit provisional
residue systematically with broader terminology, current/open work, package registries, and leads
from the first pass. Then run `definition-open-ended-prior-art-search`, the intentionally
unconstrained search task immediately before the gate. Its agents are asked to find *anything* that
can avoid fresh definition work, including sources outside the known corpus and local search
engines, and to follow newly discovered repositories/projects/citations recursively. Exact dated
search evidence stays in the canonical mapping row. Only a survivor carrying
`[residue-search-audited]` may remain `unmatched`. Repeat until the final open-ended task finds no
new viable route and the generated search/residue-search population is empty. Only then does
Milestone 1 (`definition-mapping-convergence`) transition the programme into Sweep III.

Whole-source Mapping completion is still stated only in
[the corpus status ledger](corpus/foundational-corpus-status.md) and still ultimately requires every
source unit before the programme finishes Sweep II. The definitional milestone is narrower: it gates
Sweep III and does not wait on unrelated theorem/remark/example mappings.

For **every** source-unit ID, search existing formalization work before constructing any local formalization queue.

The mandatory search surface includes:

- pinned Mathlib source;
- current upstream Mathlib, relevant source history, and open PRs;
- the live [`formalization-corpus`](https://github.com/dzackgarza/formalization-corpus): use its
  [Pages search](https://dzackgarza.github.io/formalization-corpus/) and, for systematic work, the
  live API through `scripts/formalization_corpus.py` or a client generated from the
  [OpenAPI reference](https://dzackgarza.github.io/formalization-corpus/api.html). The live
  OpenAPI document is authoritative for paths, methods, and schemas; its `SOURCES.md` is the
  canonical external-repository registry, but API hits must still be pinned to actual upstream
  commits/paths;
- Loogle, LeanSearch, Mathlib docs, and the local source atlas;
- Lean Reservoir and every discoverable packaged Lean project;
- broad GitHub code/repository search across all discoverable Lean repositories, especially open
  work/history or sources not yet indexed by the hosted corpus;
- Rocq, Agda, Isabelle, and other proof-assistant repositories indexed by `formalization-corpus`,
  when they supply an implementation that can serve as a reference rather than requiring fresh
  mathematical invention;
- local mirrored/reference corpora and statement banks such as `formal-conjectures` where
  relevant.

Search standard names, source theorem names, synonyms, namespaces, and expected type/statement
shapes. Inspect candidate declarations and hypotheses; string similarity is not a match.

Each unit must end in exactly one route class:

- `mathlib` — use the canonical Mathlib declaration/proof;
- `project-existing` — use the existing canonical LeanCategories owner;
- `package-import` — import an external Lean package;
- `reference-port` — a proof-assistant implementation exists but is not directly importable here; preserve the exact repository/revision/path/declaration/license provenance and port/adapt it later rather than rederive it;
- `unmatched` — no acceptable implementation source was found. During source-local adjudication this
  is provisional even after `[negative-search-complete]`; it becomes greenfield-eligible only after
  the separate open-ended residue audit records `[residue-search-audited]` with auditable evidence.

- [x] Record declaration names, repository/package, commit/tag, path, license,
  toolchain/Mathlib compatibility, and mathematical generality for every mapping.
- [x] Import usable packages rather than reimplement them.
- [x] Preserve non-importable Lean implementations as reference implementations rather than
  re-derive their mathematics.
- [x] Put **only** `unmatched` units into a greenfield formalization queue.

## 3. Sweep III — realize the complete definitional layer

Plan: [PLAN-FOUNDATIONAL-CORPUS-DEFINITION-SWEEP](.agents/plans/features/FEATURE-FOUNDATIONAL-CORPUS/plans/PLAN-FOUNDATIONAL-CORPUS-DEFINITION-SWEEP/PLAN-FOUNDATIONAL-CORPUS-DEFINITION-SWEEP.md).

Sweep III starts only after **Milestone 1**, `definition-mapping-convergence`, closes corpus-wide for
the definitional layer. This is deliberate: the greenfield queue is the complement of discovered
prior art, so realizing early sources while later residue has not yet undergone open-ended search
would freeze avoidable owned definitions into the dependency graph.

Then traverse each source in v3 order according to its verified mapping:

- reuse `mathlib`, `project-existing`, and `package-import` owners directly;
- port/adapt `reference-port` implementations with exact provenance;
- author new Lean mathematics only for `unmatched [residue-search-audited]` units.

- [ ] Realize every definition, construction, category, morphism class, functor, natural
  transformation, predicate, notation-bearing object, and universal construction.
- [ ] Define missing ambient categories and structural functors rather than introducing local
  stand-ins inside downstream subjects.
- [ ] Place every definition at the lowest mathematical owner that generates it.
- [ ] Re-read the original prose source after implementation and verify the actual Lean declaration
  clause-by-clause: data, hypotheses, quantifiers, equations/coherences, variance, representative
  conditions, and claimed generality. Do not infer fidelity from a familiar name or successful build.

Sweep III includes proofs intrinsic to making definitions well-defined: category/functor laws,
quotient well-definedness, independence of representatives, closure, and analogous structural
obligations. It does not absorb the source's general lemma/theorem programme.

After the last source realization, run `definition-source-conformance` across the complete open
programme. Milestone 2 (`definition-realization-convergence`) closes only when every definitional
unit survives that final source audit. Completion of that milestone is the broad foundational-DSL
milestone. Advanced definitional work may draw on this vocabulary even while Sweep IV is incomplete;
a consumer requiring an unfinished theorem depends on that theorem specifically.

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

### The whole-source ledger is intentionally too coarse to schedule individual units

The [corpus status ledger](corpus/foundational-corpus-status.md) is scored per
source per sweep. A checkbox means the sweep is complete for the entire source, and partial chapter progress deliberately does
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
The generated frontier follows the live ledger and does not duplicate its changing counts in
this hand-written TODO.

## 5. Legacy definition catalogues

The older per-source definition catalogues in `corpus/definition-catalogue-*.md` are
superseded by the Sweep-I unit catalogues. They stay as cross-checks and mapping hints. They do
not define source scope, and they never enlarge the admitted corpus.

The four sweep plans, frozen source manifest, and central status ledger are collected under
[FEATURE-FOUNDATIONAL-CORPUS](.agents/plans/features/FEATURE-FOUNDATIONAL-CORPUS/FEATURE-FOUNDATIONAL-CORPUS.md).
The detailed geometry gap inventory remains `PLAN-missing-prerequisite-theory-roadmap`. GitHub
issues #22 and #30–#41 continue to own live implementation dependencies, but they do not replace
the corpus-wide four-sweep programme.

---
type: reference
title: Provenance contract for FC05 C06
description: '# Provenance contract for FC05 C06'
tags:
- project
- reference
timestamp: '2026-09-06T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# Provenance contract for FC05 C06

# Provenance contract for FC05 C06

- Project-first search was performed at repo HEAD `f90173886bc881c2d43c0a7eb2d9fe7f110ac9a5`. Later clause-wise remap work credits project declarations for the C06 clauses they own; the baseline search found no complete standalone C06 owner.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0 and directly project-compatible. Every `P` row target was inspected at this revision.
- Current Mathlib was refreshed on 2026-09-06 at `H=5aedf732b6987e8c26ab3c9ebc855314f82b045f`. H-only declarations are not treated as project-compatible without an independently justified import route. The H audit did not close the remaining strict C06 bundles.
- `C=ccc3323c6750abca25b49b35106f54eb3a398509` is `git@github.com:kbuzzard/ClassFieldTheory.git`, Apache-2.0, Lean 4.33.0-rc1. Its exact augmentation-ideal, regular-invariants, and cyclic Tate declarations are cited on U007, U011 and U021. These are `reference-port`, not `package-import`, because the audited toolchain differs from the project Lean 4.33.0 pin.
- `T=167a73f2577fa7a600ee7977e0db599f12d92389` is `git@github.com:TauCetiProject/TauCeti.git`, Apache-2.0, Lean 4.34.0-rc2. Its fixed-action/factor-set/H² extension declarations own U065 and U067–U072; its smooth-discrete coefficient interface owns U141. All are `reference-port` for the same toolchain reason.
- Sweep III U007 accepts the TauCeti augmentation port already integrated in `LeanCategories/Algebra/MonoidAlgebra.lean` (original local integration `bed16b18`, FC05 source tag `e97da905`). The coefficient-sum homomorphism and its kernel are the complete Definition 6.1.5 definition layer at `R=ℤ`; `augmentationGenerators` records `{g-1}` while the assertion that they span the kernel remains theorem work. The owner builds successfully and temporary probes check coefficient summation, generator membership, and the separating case `1 ∉ I`. Reference origin remains TauCeti `d6214142a5e6403ba4f977246f1fc16418d561e4`, Apache-2.0.
- TauCeti's profinite continuous-cohomology development is not blanket coverage. `TauCeti/RepresentationTheory/Homological/ContCohomology/FiniteQuotient.lean` explicitly constructs the finite-quotient system while stating that the colimit theorem identifying it with continuous cohomology is not supplied there. Its low-degree files likewise do not supply the source's full H² classification of profinite extensions. U143–U150 therefore stay unmatched unless the complete source bundle exists.
- Mapping discovery was refreshed on 2026-09-14 against formalization-corpus index `2ebd72a616f97b1c30bcae966d02df6763f4b684`. For U016, FLT `81d8bee0f708ac41cb975da76ed3c43ad99fae72` has a proof-complete all-degree continuous **cup** product for a single group, TauCeti current `af95f43d2fd4724510500f3b9dba380bf1339005` has explicit same-group cups through degree two, Atlas has an unfinished singular-cohomology cross product, and Agda Cubical `c2d05f7909c2254e2dfa5783b1bc88d99b878b87` has topological sphere-product cohomology; none is Weibel's two-group external group-cohomology product, so U016 remains unmatched after product-group/tensor-resolution/cross-prover searches. In contrast, current TauCeti exactly closes U072: `GroupExtension.sectionDiff` constructs the comparing 1-cochain, `isMulCoboundary₂_div` proves the factor-set quotient is its 2-coboundary, and `cohomologyClass_factorSet_eq` proves the `H²` class is section-independent. The two cited files contain no `sorry`, `admit`, or axioms, so U072 is promoted to `reference-port` at that exact revision.
- The same 2026-09-14 pass exhausted the remaining definitional C06 gaps in this cluster. U076 has no checked four-term/crossed-extension `H³` cocycle constructor in current Mathlib, TauCeti, or the indexed cross-prover sources; the project's `FourTermCrossedExtension.Choices` still accepts the desired three-cochain rather than deriving it. U090 retains Mathlib's exact diagonal restriction and records FLT's proof-complete all-degree continuous cup product as prior art, but no checked comparison transports that construction to the ordinary `groupCohomology` functor and U016's two-group external product is still absent. U110 was searched under the free-presentation, Schur-multiplier, Hopf-formula, `R∩[F,F]`, and universal-central-extension formulations; no Lean or indexed non-Lean source constructs Weibel's central quotient together with the perfect-group restriction. These rows therefore retain `unmatched` with current negative evidence rather than inheriting the 2026-09-06 search.
- P/H make `A^H` and `A_H` into `G/H`-representations, but the audit found no checked adjunction with quotient restriction matching all of U098. The pinned low-degree inflation/restriction exactness is not substituted for the full LHS five-term sequences U100 without an LHS spectral sequence.
- Pinned `Rep.barResolution` owns the unnormalized bar differential and resulting (co)homology computations. It does not supply Weibel's normalized quotient in which a symbol containing `1` vanishes. U048, U050, U052 and U056 are therefore not over-credited, while U049, U051 and U053–U055 receive their exact P routes.
- U121 is matched by `ProperlyDiscontinuousSMul` together with `ContinuousConstSMul` and freeness via `IsCancelSMul`: the neighborhood theorem gives disjointness for translates not fixing the base point, and freeness converts that to `g ≠ 1`.
- `N` is dated 2026-09-06 negative evidence after project-first inspection, P, H/current Mathlib, the exact C/T revisions above, relevant open/current/indexed searches already recorded in the audit session, and broad Lean-source searches. A prerequisite, low-degree shadow, or one clause of a bundled statement is not credited as a route for the whole row.

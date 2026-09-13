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

- Project-first search was performed at repo HEAD `f90173886bc881c2d43c0a7eb2d9fe7f110ac9a5`. No project declaration owns a complete C06 source row under strict bundle semantics.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0 and directly project-compatible. Every `P` row target was inspected at this revision.
- Current Mathlib was refreshed on 2026-09-06 at `H=5aedf732b6987e8c26ab3c9ebc855314f82b045f`. H-only declarations are not treated as project-compatible without an independently justified import route. The H audit did not close the remaining strict C06 bundles.
- `C=ccc3323c6750abca25b49b35106f54eb3a398509` is `git@github.com:kbuzzard/ClassFieldTheory.git`, Apache-2.0, Lean 4.33.0-rc1. Its exact augmentation-ideal, regular-invariants, and cyclic Tate declarations are cited on U007, U011 and U021. These are `reference-port`, not `package-import`, because the audited toolchain differs from the project Lean 4.33.0 pin.
- `T=167a73f2577fa7a600ee7977e0db599f12d92389` is `git@github.com:TauCetiProject/TauCeti.git`, Apache-2.0, Lean 4.34.0-rc2. Its fixed-action/factor-set/H² extension declarations own U065 and U067–U072; its smooth-discrete coefficient interface owns U141. All are `reference-port` for the same toolchain reason.
- TauCeti's profinite continuous-cohomology development is not blanket coverage. `TauCeti/RepresentationTheory/Homological/ContCohomology/FiniteQuotient.lean` explicitly constructs the finite-quotient system while stating that the colimit theorem identifying it with continuous cohomology is not supplied there. Its low-degree files likewise do not supply the source's full H² classification of profinite extensions. U143–U150 therefore stay unmatched unless the complete source bundle exists.
- P/H make `A^H` and `A_H` into `G/H`-representations, but the audit found no checked adjunction with quotient restriction matching all of U098. The pinned low-degree inflation/restriction exactness is not substituted for the full LHS five-term sequences U100 without an LHS spectral sequence.
- Pinned `Rep.barResolution` owns the unnormalized bar differential and resulting (co)homology computations. It does not supply Weibel's normalized quotient in which a symbol containing `1` vanishes. U048, U050, U052 and U056 are therefore not over-credited, while U049, U051 and U053–U055 receive their exact P routes.
- U121 is matched by `ProperlyDiscontinuousSMul` together with `ContinuousConstSMul` and freeness via `IsCancelSMul`: the neighborhood theorem gives disjointness for translates not fixing the base point, and freeness converts that to `g ≠ 1`.
- `N` is dated 2026-09-06 negative evidence after project-first inspection, P, H/current Mathlib, the exact C/T revisions above, relevant open/current/indexed searches already recorded in the audit session, and broad Lean-source searches. A prerequisite, low-degree shadow, or one clause of a bundled statement is not credited as a route for the whole row.

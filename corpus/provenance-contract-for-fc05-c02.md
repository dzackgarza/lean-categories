---
type: reference
title: Provenance contract for FC05 C02
description: '# Provenance contract for FC05 C02'
tags:
- project
- reference
timestamp: '2026-09-11T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# Provenance contract for FC05 C02

# Provenance contract for FC05 C02

# Provenance contract for FC05 C02

# Provenance contract for FC05 C02

- Project-first search was performed at repo HEAD `f901738`. `LeanCategories/Homological/DerivedDimension.lean` owns the source-facing higher-left-derived vanishing predicate `LeanCategories.Homological.IsCoacyclicFor`; this is the canonical project route for U041. Other C02 project homological files reexport or specialize Mathlib owners rather than replacing them.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0. P directly supplies categorical projectives/injectives, enough-projective/enough-injective structures, projective and injective resolutions and comparison homotopies, generic left/right derived functors, intrinsic derived-category Ext and both resolution computations, adjunction/exactness machinery, sheaf stalk/skyscraper and (co)image functors, arbitrary (co)limits in abelian categories from products/coproducts, filtered categories, ModuleCat filtered colimits, AB5, and the Hom-complex/homotopy-category cohomology theorem.
- Correction rechecked 2026-09-11: U030 is already exact in pinned Mathlib. `DomMulAct R` is the `MulOpposite R` domain-action type, and `AddMonoidHom.instDomMulActModule` gives `Module Rᵈᵐᵃ (B →+ A)` for every left `R`-module `B`; `DomMulAct.smul_addMonoidHom_apply` specializes to `(DomMulAct.mk r • f) b = f (r • b)`. The former U030 negative route overlooked this generic bundled-Hom instance.
- Two source-shaped infrastructure assertions were compile-checked against P: abelian sheaves on a topological space infer `EnoughInjectives` through Mathlib's Grothendieck-category machinery, and an abelian category with arbitrary coproducts (respectively products) infers all small colimits (respectively limits). These justify U036/U061/U063 without weakening their existence claims.
- The source is explicitly written for an arbitrary associative ring with right and left modules. Mathlib's standard `TensorProduct` and the monoidal/closed structure on `ModuleCat R` still require a commutative scalar ring; `TensorProduct.liftAddHom` itself notes that the first action should be a right action but is currently represented using commutativity. Therefore the noncommutative tensor-Hom, tensor, Tor, tensor-complex, and Tor-balancing rows U031 and U054-U057/U074-U075 are not credited from commutative-base Mathlib.
- Current Mathlib was rechecked at `H=5aedf732b6987e8c26ab3c9ebc855314f82b045f`. Searches at H did not add a δ-functor abstraction, Horseshoe lemma, generic syzygy owner, noncommutative module tensor/Tor, Tor balancing, Acyclic Assembly Lemma, balanced-multivariable-functor definitions, or the derived direct-sum/filtered-colimit preservation theorems left unmatched here.
- Open Mathlib PR search on 2026-09-06 for δ-functors, Horseshoe, Tor balancing, homology/colimit, and sheaf enough-injectives found no applicable open PR. Thus no C02 route is attributed to an open Mathlib PR.
- `leanprover-community/lean-liquid@087fffad55dc1dd8d54ab35c9816926a45b8c0fd` was rechecked at its current HEAD. Its legacy Lean 3 `src/for_mathlib/universal_delta_functor/basic.lean` implements a covariant cohomological δ-functor category, morphisms, universality, effaceability, and `universal_of_effaceable`, but the repository has no LICENSE/COPYING file, uses Lean 3.48 with Mathlib `5947fb69058f2fa5ac8a4476182707a52f5cf2be`, and does not directly implement the homological dual/source left-derived package. It is therefore evidence of prior Lean work but not an acceptable `reference-port` under this mapping contract.
- U071 has one exact revision-specific external owner: `TauCetiProject/TauCeti@a8e6879667d6e38093b899315881b4f7b8e4b55a`, Apache-2.0, Lean `v4.34.0-rc2`, Mathlib `5fcc6656b48daf74b23607447c65ea30934f1b8f`. `TauCeti/Algebra/Homology/ShortComplex/Colimit.lean::HomologicalComplex.preservesHomologyOfShape` proves that homology preserves any exact colimit shape. Specializing to a filtered shape in an AB5 category is exactly U071, so the row is a revision-specific `reference-port`, never pinned Mathlib.
- Pinned `CategoryTheory/Monoidal/Tor.lean` explicitly records that the two Tor variable constructions are expected to be isomorphic but that this balancing has not been proved there. This is positive evidence for the strict negatives U057/U075 rather than grounds to count them as Mathlib coverage.
- The older definition-only Weibel catalogue is not route authority. Its generic `Tor` and “balanced functor” hints lose the source's noncommutative right/left-module generality and do not provide Weibel's balanced-functor predicates; the Sweep-II rows here use the stricter checked interfaces instead.
- Sweep III recheck on 2026-09-11 supersedes two C02 negatives: U045 now has the project-owned source kernel terminology `ProjectiveResolution.syzygy`/`syzygyι` at `2cb95566c780301276a432387277e67f900cb021`; Mathlib's similarly named `Projective.syzygies` is instead a projective cover of the kernel. U080 now has the project-owned mixed-variance right-balanced predicate `IsRightBalanced` at `6275e09dd58df3f335c45442205790ddd4f5f1dc`, with contravariance represented by opposite input categories and the pinned projective/opposite-injective instances.
- `N` denotes dated 2026-09-06 negative evidence after project-first inspection, P, H/current Mathlib, open-PR search where relevant, and targeted external Lean search. Clause-wise remap work credits adjacent primitives and specializations exactly where their hypotheses and conclusions match; residual arbitrary-ring or comparison clauses remain negative only when no checked route was found.

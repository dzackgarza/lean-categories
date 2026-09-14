---
type: reference
title: Provenance contract for FC05 C01
description: '# Provenance contract for FC05 C01'
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
# Provenance contract for FC05 C01

# Provenance contract for FC05 C01

- Project-first search was performed at repo HEAD `f901738` (subsequently unchanged during this chapter audit). `LeanCategories/Homological.lean` reexports the canonical Mathlib homological stack and `LeanCategories/Homological/Extensions.lean` owns later extension material; no C01 source unit has a distinct project-owned implementation, so C01 has no `project-existing` route.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0. P directly supplies homological/cohomological complexes, quasi-isomorphisms, support/truncation and shift machinery, exactness, snake/homology sequences, homotopies, mapping cones, Freyd–Mitchell, abelian full/functor categories, sheaves/sheafification, exact functors, and additive Yoneda. Source-shaped assemblies for U041 (`QuasiIso φ ↔ (mappingCone φ).Acyclic`) and U063 (all representable-Hom exactness tests imply exactness) were independently compiled against P.
- Current Mathlib was rechecked at `H=5aedf732b6987e8c26ab3c9ebc855314f82b045f`. Targeted current-source searches found no product totalization, algebraic mapping cylinder of a map, weakly-effaceable functor quotient, exponential-sequence sheaf counterexample, or packaged `S ⥤ L` long-exact-sequence functor. Current additions therefore do not change the negative routes recorded here.
- The older definition-only Weibel catalogue is not treated as route authority. In particular, its mapping-cylinder entry points to `HomologicalComplex.cylinder`, which is a cylinder of a complex rather than Weibel’s cylinder of a map, and its split-complex entry conflates the weaker equation `d=dsd` with a chain contraction `ds+sd=id`; both overmatches are rejected here.
- External search rechecked `deancureton/sphere-six-complex@895c0a0661501581c34d42fea3c553d4f0ee43b1` (Apache-2.0, Lean `v4.34.0-rc1`, Mathlib fork revision `97d303eb50436be7c4bac4388bdb49459ae9140b`). It defines the canonical simplicial-to-singular chain map and the proposition that it is a quasi-isomorphism, but its proof files only reduce the assertion to additional cover-small quasi-isomorphism hypotheses and then special boundary-seven hypotheses; it does not prove the general triangulation/simplicial-realization comparison needed for U008. It is therefore negative evidence, not a reference port.
- External effaceability search rechecked `leanprover-community/lean-liquid@087fffad55dc1dd8d54ab35c9816926a45b8c0fd`. Its `universal_delta_functor/basic.lean` defines effaceability of δ-functors for the universal-δ-functor theorem, not Weibel’s weakly-effaceable contravariant functors, `W(M)`, or the localizing quotient of U064–U067. It is not a route for those rows.
- External Yoneda search rechecked `mattrobball/BridgelandStability@b858822408838e40cf5077aea233dc1dc660c461`; its exactness argument invokes Mathlib’s `Functor.reflects_exact_of_faithful` and `preadditiveYoneda`, confirming the pinned owner rather than supplying a separate implementation.
- Targeted GitHub Lean searches for map-level algebraic mapping cylinders, product totalizations, weakly-effaceable functors, bundled homology-sequence functors, and the source split-complex/counterexample interfaces returned no exact implementation. `N` is dated 2026-09-06 negative evidence after project, P, H/current, and these external searches.
- Route decisions are clause-wise. Adjacent theorems and stronger-but-different statements are credited only for the clauses they actually supply; unsupported comparison or existence clauses remain explicit residuals in the affected rows.

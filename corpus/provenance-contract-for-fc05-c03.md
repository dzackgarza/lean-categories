---
type: reference
title: Provenance contract for FC05 C03
description: '# Provenance contract for FC05 C03'
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
# Provenance contract for FC05 C03

# Provenance contract for FC05 C03

# Provenance contract for FC05 C03

# Provenance contract for FC05 C03

- Project-first search was performed at repo HEAD `f901738`. `LeanCategories/Homological/Extensions.lean` exports `LeanCategories.Homological.Extension` and `Extension.Equiv` for arbitrary rings. Its module docstring mentions the Baer sum, but no Baer-sum operation or Ext¹ classification is implemented there. Pinned `ShortComplex.Splitting` supplies the split-sequence side, so U036 is the only project-existing C03 route.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0. `Module.FinitePresentation` is defined for arbitrary semirings/rings and gives the exact finite-generator/finite-relation presentation of U014. `CharacterModule.dual_surjective_iff_injective`, specialized to scalar ring ℤ on the underlying additive map, gives U013. Generic `Limits.lim` and `Functor.rightDerived` provide the derived inverse-limit construction U043 and its countable-tower specialization U044 under the usual completeness/enough-injectives assumptions.
- The chapter continues Weibel's arbitrary-associative-ring convention. P/H `Module.Flat` is declared only under `[CommSemiring R]`, and `Mathlib/LinearAlgebra/TensorProduct/Basic.lean` still uses a commutative scalar ring (with an explicit TODO/comment about the missing right-action generalization). Therefore the arbitrary-ring flatness/Tor, central-localization, character-module, and tensor-based rows are not credited from commutative Mathlib implementations.
- Current Mathlib was rechecked at `H=5aedf732b6987e8c26ab3c9ebc855314f82b045f`. Targeted source search found no Baer sum/Yoneda-Ext classification, no explicit Tor/Ext calculations required by C03, no `lim¹`/Milnor/Roos development, and no Künneth or universal-coefficient theorem matching the source rows.
- Pinned `CategoryTheory/CofilteredSystem.lean` provides `Functor.IsMittagLeffler` and stabilization/eventual-range theorems. The project later supplied Weibel's additional trivial Mittag–Leffler definition and its elementary implication, while the `Mittag–Leffler ⇒ lim¹=0` theorem remains a separate unsupported result clause where recorded in the mapping.
- The project/P/H extension searches found no Baer-sum construction, abelian-group structure on extension classes, or classification by `Abelian.Ext`. Generic intrinsic Ext and its projective/injective resolution computations were already mapped in FC05 C02; they do not by themselves realize the C03 extension-classification rows U037–U042.
- External search on 2026-09-06 for Künneth, universal coefficient, Milnor exact sequences, Mittag–Leffler/right-derived limit, `lim1`, Baer sum, and Yoneda Ext found no proved source-general implementation. `deancureton/sphere-six-complex@895c0a0661501581c34d42fea3c553d4f0ee43b1` has a file named `ClassicalIntegralUCTBoundary.lean`, but its general integral singular-cohomology UCT is introduced as `public axiom classicalIntegralSingularCohomologyUCT`; it is not a proof and is not a mapping route.
- The older definition-only Weibel catalogue is not route authority. Its flat/Tor hints silently lose the source's arbitrary-ring right/left-module generality, and its Mittag–Leffler/AB4* hints do not supply the complete source bundles checked here.
- `N` denotes dated 2026-09-06 negative evidence after project-first inspection, P, H/current Mathlib, and targeted external Lean search. Clause-wise remap work reuses generic infrastructure and specializations for the statements they genuinely supply; explicit calculation/comparison clauses remain negative only when no checked route for those clauses was found.
- Sweep III recheck on 2026-09-11 supersedes the U033 negative. `LeanCategories/Homological/FiniteFreeResolution.lean` now owns the source convention `IsRightNoetherianRing R := IsNoetherianRing Rᵐᵒᵖ`, the finitely-generated-right-module finite-presentation theorem, and a noncanonical recursively constructed augmented resolution by finite-rank free modules with exactness proved in degree zero and every positive degree. Final packaging commit: `8ea3f3cdf2b1a6100cf6e12deecb1392d80f16d7`; direct Lean validation passed.
- Sweep III recheck on 2026-09-11 supersedes the U040 negative. `LeanCategories/Homological/Extensions.lean` now exports the literal Baer construction: `baerFiber` is the kernel of the difference of the two quotient maps, `baerSkew` is the skew diagonal, `baerMiddle` is the quotient by its range, and `baerSum` packages the induced short exact sequence. Injectivity, surjectivity, and exactness are proved locally. Final packaging commit: `46fe0d30487afad2f793f1a139e6ae1627884a3b`; direct Lean validation passed.

---
type: reference
title: Provenance contract for FC05 C07
description: '# Provenance contract for FC05 C07'
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
# Provenance contract for FC05 C07

# Provenance contract for FC05 C07

- Project-first search was performed at repo HEAD `f90173886bc881c2d43c0a7eb2d9fe7f110ac9a5`. Later clause-wise remap work credits project declarations for the C07 clauses they own; the baseline search found no complete standalone C07 owner.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0 and directly project-compatible. Every `P` target cited in the chapter table was inspected at that revision. Two composite interfaces were also compiled against the pinned project environment: the UEA map induced by a Lie homomorphism (from `UniversalEnvelopingAlgebra.lift`/`hom_ext`) and the exact Weibel-sign affine Killing cocycle used in U074.
- Current Mathlib was refreshed on 2026-09-06 at `H=5aedf732b6987e8c26ab3c9ebc855314f82b045f`. H-only declarations are not treated as project-compatible. The current `Mathlib/Algebra/Lie/Cochain.lean` still lists comparison with the Chevalley–Eilenberg complex as future work; targeted current searches found no Lie-module category, Lie derived-functor (co)homology, Hochschild–Serre spectral sequence, PBW completion, or universal-central-extension theory closing the unmatched bundles.
- `T=bf90834bad4dd74ef016776cd6b4843eebb49f67` is `git@github.com:TauCetiProject/TauCeti.git`, Apache-2.0, audited at Lean 4.34.0-rc2. U007 is an exact reference-port through `TauCeti/Algebra/Lie/Derivation.lean::TauCeti.derivationLieAlgebra`. Other TauCeti Lie infrastructure was audited but is not promoted when its hypotheses or conclusion are narrower than the source bundle.
- In particular, TauCeti's PBW development at T proves the surjective half of the symmetric-algebra-to-associated-graded map but not injectivity, so U027–U029 remain unmatched. Its complete-reducibility theorem is stated over an algebraically closed field, narrower than Weibel's characteristic-zero-field theorem U062. Its Casimir development proves basis formulas, centrality, and nontrivial-module injectivity, but the audit found no theorem placing the source Casimir element in the augmentation ideal, so bundled U059 remains unmatched.
- Pinned Mathlib has no category of modules over a fixed Lie algebra. TauCeti explicitly records the same limitation. Therefore the pointwise U(L)-module/Lie-module dictionary is not upgraded to the natural categorical isomorphism U023, and the source enough-projectives/injectives statement U024 is not inferred from ordinary module-category facts.
- Pinned/current Mathlib and TauCeti contain extension and 2-cocycle infrastructure, but no equivalence-of-extensions structure, H² classification, or universal-central-extension package matching U044–U046 or U067–U072. Similarly no checked declaration supplies the Hochschild–Serre spectral sequence or its low-degree exact sequences U041–U042.
- The source U055 is bundled: besides Cartan's semisimplicity/Killing criterion it asserts nondegeneracy of the trace form for a semisimple matrix Lie algebra. The latter whole-source interface was not found, so the row is not partially credited. U056's direct-product-of-simple structure theorem and semisimplicity of every ideal likewise exceed the checked structural semisimplicity API.
- The source U003, U004, U008, U009, U012, U015 and U016 contain clauses beyond the adjacent pinned definitions found in the audit: respectively an arbitrary-module zero-bracket constructor, universal abelianization, free Lie algebra on a module (not merely a set), the strictly-upper-triangular nilpotence example, the upper-triangular counterexample, an additive Lie-module category, and the exact trivial-module/invariant/coinvariant functor package. The mapping rows credit the available clauses and leave precisely these residual constructions/examples unsupported where no checked owner was found.
- `N` is dated 2026-09-06 negative evidence after project-first inspection, P, H/current Mathlib, the exact T revision above, recorded open/current/indexed searches, GitHub code/PR searches, and broad Lean-source searches. A prerequisite, a derived consequence requiring an unformalized source theorem, a stronger restriction on the base field, or one clause of a bundled row is not credited as the route for that row.

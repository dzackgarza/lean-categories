---
type: reference
title: Provenance contract for FC08 C08
description: '# Provenance contract for FC08 C08'
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
# Provenance contract for FC08 C08

# Provenance contract for FC08 C08

- Canonical source block: FC08 Lee, Chapter 8, `FC08-C08-U001`–`FC08-C08-U069`, exactly 69 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order followed the Sweep-II plan: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then targeted current/indexed/external Lean searches. No `project-existing`, `package-import`, or `reference-port` C08 owner survived strict whole-row checking.
- C08 has 6 pinned `mathlib` rows and 63 dated `unmatched` rows. Positive rows are: U023, U045, U047, U048, U050, U067.
- The controlling semantic boundary is inherited from promoted C03 and was rechecked for C08. Lee’s tangent vectors are the point-derivation model formalized by `PointDerivation`; Mathlib’s mature vector-field, tangent-bundle, local-frame, pullback, and `mlieBracket` APIs use the separate standard `TangentSpace` model. Pinned `DerivationBundle.lean`/`LeftInvariantDerivation.lean` document that the finite-dimensional C∞ real identification with the usual tangent space/vector fields should hold, but do not formalize it. Exact searches at P and H again found no `PointDerivation ≃ TangentSpace` or vector-field/global-derivation equivalence. Therefore C08 does not silently route Lee vector-field rows through standard-tangent APIs that C03 already treated as unbridged.
- This boundary excludes several otherwise excellent matches deliberately. `ContMDiffSection` gives smooth standard-tangent sections and their real vector-space operations; `ContMDiff.smul_section` gives smooth-function multiplication; `LocalFrame.lean` gives local frames and coefficient smoothness criteria; `VectorField.mlieBracket` proves smoothness and the full bracket laws. `/tmp/fc08-c08-witness.lean` compiled all four clauses of Lee’s U039 bracket proposition in the standard tangent model, plus the smooth-section operations. Those checks establish adjacency, not equivalence to Lee’s derivation-defined vector fields.
- U023 is independent of the missing bridge: `Derivation ℝ C^∞⟮I,M;ℝ⟯ C^∞⟮I,M;ℝ⟯` exactly owns Lee’s definition of a global derivation. U024 remains unmatched precisely because the converse identification of such derivations with smooth vector fields is not formalized.
- U045, U047, U048, U050, and U067 are likewise model-independent algebraic interfaces. Mathlib’s generic `LieAlgebra`, `LieSubalgebra`, `LieHom`/`LieEquiv`, `IsLieAbelian`, and Lie-homomorphism-to-`Module.End`/faithfulness interfaces specialize exactly to Lee’s real finite-dimensional definitions. The audit witness typechecked these interfaces at the pin.
- For Lie groups, P has substantial adjacent machinery: `GroupLieAlgebra I G := TangentSpace I 1`, `mulInvariantVectorField`, smoothness and bracket invariance of those constructed fields, and the separate `LeftInvariantDerivation` Lie algebra. But there is no checked evaluation equivalence identifying Lee’s Lie algebra of all left-invariant vector fields with `T_eG`, and no bridge between the standard-tangent and derivation models. Consequently U043–U044 and U051–U059 are not inferred from these constructions.
- The map/functor boundary is also explicit: neither P nor current H has a `GroupLieAlgebra` Lie homomorphism induced by a smooth group homomorphism, or a Lie functor. Targeted H searches found no `GroupLieAlgebra.*LieHom`, `LieHom.*GroupLieAlgebra`, `LieSubgroup`, or invariant-field evaluation equivalence. U060–U066 remain unmatched.
- The submanifold-dependent rows U032–U034, U042, and U064–U066 inherit C05’s separate blocker: P/H still have no general embedded/immersed submanifold or Lie-subgroup package.
- The orthonormal/global-frame block has partial infrastructure only. `LocalFrame.lean` explicitly refers to a planned `OrthonormalFrame.lean`, which is absent at both P and H; no named parallelizability theorem for Lie groups was found. U018–U021 and U055–U056 therefore remain unmatched independently of the tangent-model issue.
- Targeted indexed search surfaced the current TauCeti Lie-groups roadmap, which independently records the Lie functor, closed-subgroup/Lie-subgroup theory, and Ado theorem as future targets rather than completed upstream interfaces. This was used only as secondary external evidence; route decisions are grounded in the exact checked revisions above.
- `N=2026-09-07` marks dated unmatched decisions after the prescribed search layers. Strict whole-row semantics apply uniformly.


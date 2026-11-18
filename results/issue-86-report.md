# #86 — Satake diagrams (admissible pairs) and real forms

Two new modules, both imported from `LeanCategories/All.lean`:

* `LeanCategories/Algebra/SatakeDiagramData.lean` — issue items 1 (admissible pairs and the
  category of Satake diagrams) and the `D₄` triality witness of the audit correction;
* `LeanCategories/Algebra/RealFormData.lean` — item 2 (real forms) and the *statement* of item 3.

Item 3 (Araki's classification) is **not** proved; it is stated, and its two open halves are filed
in `COMPLAINTS.md` under `#86` (LC-11). Details in §3. The whole-library gate
(`lake build LeanCategories.All`, then `just test`) is green on this tree; job counts and each
audit's result are in "The whole-library gate" at the end.

## 1. Item 1 — admissible pairs, and the category of Satake diagrams: LANDED

Source: S. Kolb, *Quantum symmetric Kac–Moody pairs*, Adv. Math. 267 (2014), Definition 2.3
(arXiv:1207.6036v2, p. 9), the finite-type case being Araki, *On root systems and an infinitesimal
classification of irreducible symmetric spaces*, J. Math. Osaka City Univ. 13 (1962), pp. 32–33.

`SatakeDiagramData.lean:299` — the four conditions of the source, with the issue's numbering:

```lean
structure IsAdmissiblePair [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (X : Finset ι)
    (τ : Equiv.Perm ι) : Prop where
  finiteType : IsFiniteTypeSubdiagram A X                                  -- (i) X of finite type
  preservesCartan : IsDiagramAutomorphism A τ                              -- τ ∈ Aut(A)
  preservesSubdiagram : PreservesSubdiagram τ X                            -- τ ∈ Aut(A, X)
  involutive : τ * τ = 1                                                   -- source (1)
  agreesWithLongestElement : AgreesWithNegativeLongestElement A X finiteType.diagonal τ
                                                                           -- source (2)
  integralZeroWeight : HasIntegralParabolicWeylPairing A X τ                -- source (3)
```

Supporting declarations, each at the line given:

| line | declaration | content |
| --- | --- | --- |
| 75 | `CartanRootLattice ι` | the root lattice `ℤΠ` as `ι → ℤ` |
| 88 | `cartanCorootPairing A v i` | `⟨v, α_i^∨⟩ = Σ_j v_j a_{ji}` |
| 98 | `cartanReflection A i` | `s_i v = v - ⟨v, α_i^∨⟩ α_i` as a `→ₗ[ℤ]` |
| 132 | `cartanReflection_involutive` | `s_i² = 1` (needs `a_{ii} = 2`) |
| 144 | `cartanReflectionEquiv A i h` | the reflection as a `≃ₗ[ℤ]` |
| 159 | `subdiagramWeylGroup A X hdiag` | `W_X = ⟨s_i : i ∈ X⟩ ≤ GL(ℤΠ)` |
| 178 | `IsLongestElementOfSubdiagram A X hdiag w` | `w ∈ W_X` and `w` sends every simple root of `X` to a negative root |
| 185 | `AgreesWithNegativeLongestElement A X hdiag τ` | `∃ w = w_X, ∀ i ∈ X, w α_i = -α_{τ i}` |
| 194, 198 | `IsDiagramAutomorphism`, `PreservesSubdiagram` | `a_{τi τj} = a_{ij}`, and `i ∈ X ↔ τ i ∈ X` |
| 223, 231, 236 | `IsGeneralizedCartanMatrix`, `cartanQuadraticForm`, `IsFiniteTypeCartanMatrix` | Kac's axioms and the positive-definiteness criterion (Kac, *Infinite-dimensional Lie algebras*, Ch. 4, Thm. 4.3) |
| 246 | `IsFiniteTypeSubdiagram A X` | the principal submatrix on `X` is of finite type |
| 280, 287 | `IsParabolicWeylVectorCoefficient`, `HasIntegralParabolicWeylPairing` | `ρ^∨_X` by `α_k(ρ^∨_X) = 1` (`k ∈ X`), then `α_j(ρ^∨_X) ∈ ℤ` |

The category (`SatakeDiagramData.lean:651–736`): objects carry the admissible-pair datum,

```lean
structure SatakeDiagram where
  index : Type u
  [fintypeIndex : Fintype index] [decEqIndex : DecidableEq index]
  cartan : Matrix index index ℤ
  black : Finset index
  tau : Equiv.Perm index
  admissible : IsAdmissiblePair cartan black tau

structure SatakeDiagram.Hom (D E : SatakeDiagram.{u}) where
  toEquiv : D.index ≃ E.index
  cartan_preserved : ∀ i j, E.cartan (toEquiv i) (toEquiv j) = D.cartan i j
  black_preserved : ∀ i, (i ∈ D.black ↔ toEquiv i ∈ E.black)
  tau_comm : ∀ i, toEquiv (D.tau i) = E.tau (toEquiv i)
```

with `CategoryTheory.Category SatakeDiagram` (`:717`) and `CategoryTheory.Groupoid SatakeDiagram`
(`:725`) — every morphism is invertible, `Hom.symm` (`:704`) is the inverse. The morphisms are the
issue's "diagram morphisms that preserve `X` and commute with `τ`" (plus preservation of the Cartan
matrix, without which a reindexing of the vertex set would forget the diagram).

### Probes (smallest inputs that decide the definition)

Run as `lake env lean` on the module; each is a closed theorem whose proof has no `sorry`.

| line | theorem | what it decides |
| --- | --- | --- |
| 317 | `isAdmissiblePair_empty (A) : IsAdmissiblePair A ∅ 1` | the split diagram: conditions (2), (3) vacuous, (i) `isFiniteTypeSubdiagram_empty` — proved for **every** `A : Matrix ι ι ℤ` |
| 529 | `satakeA1_compact_admissible : IsAdmissiblePair (CartanMatrix.A 1) Finset.univ 1` | the compact `su(2)` diagram: one black node, `-w_X = id` (the reflection `s_0` negates `α_0`) |
| 570 | `satakeA3_blackMiddle_swapped_admissible : IsAdmissiblePair (CartanMatrix.A 3) {1} (Equiv.swap 0 2)` | Kolb's Example 2.4, fourth case: a **non-trivial `τ`**; condition (3) empty because `τ` moves both white nodes |
| 614 | `satakeA3_blackEnds_admissible : IsAdmissiblePair (CartanMatrix.A 3) {0, 2} 1` | Kolb's Example 2.4, **first case**: `X = A₁ ⊕ A₁` with longest element `s_0 s_2`, `-w_X = id`; `α₂(ρ^∨_X) = -1 ∈ ℤ` at the white node |
| 675 | `satakeA3_blackFirst_not_admissible : ¬ IsAdmissiblePair (CartanMatrix.A 3) {0} 1` | Kolb's Example 2.4, second case: `α_1(ρ^∨_X) = -1/2 ∉ ℤ` |
| 689 | `satakeB2_blackShort_admissible : IsAdmissiblePair (CartanMatrix.B 2) {1} 1` | `B₂` with the **short** node black: `α_0(ρ^∨_X) = a_{01}/2 = -1 ∈ ℤ` |
| 722 | `satakeB2_blackLong_not_admissible : ¬ IsAdmissiblePair (CartanMatrix.B 2) {0} 1` | `B₂` with the **long** node black: `α_1(ρ^∨_X) = a_{10}/2 = -1/2 ∉ ℤ` |

Searched before the two declarations this case needed (LC-09):
`python3 scripts/formalization_corpus.py search "longest element parabolic"` gives TauCeti's
`TauCeti/GroupTheory/Coxeter/LongestElement.lean` (`CoxeterSystem.IsLongest`, the length identity
`ℓ (u * w₀) + ℓ u = ℓ w₀`) — **not used**: its carrier is a `CoxeterSystem M W`, and this file has
no Coxeter presentation of `W_X`, only its action on the root lattice, so building one to obtain
`s_0 s_2` would cost far more than the two rewrites; `… search "w0 simple root negative"` gives only
TauCeti `F4/ShortRoot` files and nothing reusable. Mathlib searched at the pinned revision for
`Finset.sum_pair`, `Finset.sum_coe_sort`, `map_neg` (all present and used) and for the product
action on linear automorphisms, where `LinearEquiv.mul_apply` is deprecated in favour of
`mul_apply_eq_comp`.

The two negative probes go through `exists_int_eq_half_mul_of_singleton` (`:493`), which reduces
condition (3) at a single black node to `a_{ji}/2 ∈ ℤ`; `parabolicWeylVectorCoefficient_singleton`
(`:483`) proves the coefficient is `1/2` there, from the defining equation. The finite-type
hypothesis on the small black-node sets is `isFiniteTypeSubdiagram_singleton` (`:371`) and
`isFiniteTypeSubdiagram_pair` (`:401`), both proved from the positive-definiteness criterion.

Kolb's Example 2.4 **first case** `({1,3}, id)` also landed (`SatakeDiagramData.lean:614`,
`satakeA3_blackEnds_admissible : IsAdmissiblePair (CartanMatrix.A 3) ({0, 2} : Finset (Fin 3)) 1`,
nodes `0,2` being the source's `1,3`). It needed the two declarations the previous turn named:

* `sum_pair_subtype` (`:490`), `∑ l : ↥{i, j}, f ↑l = f i + f j` for `i ≠ j`, from
  `Finset.sum_coe_sort` and `Finset.sum_pair` — the summands in both conditions of
  `IsAdmissiblePair` factor through the projection when the Weyl-vector coefficients are the
  constant `1/2`, which is what makes the factored form enough (a version for an arbitrary
  subtype summand is not needed);
* `cartanReflection_mul_simpleRoot_of_disjoint` (`:362`), `(s_i * s_j) α_i = -α_i ∧
  (s_i * s_j) α_j = -α_j` for `a_{ii} = a_{jj} = 2` and `a_{ij} = a_{ji} = 0` — the product of two
  commuting reflections as the longest element of the `A₁ ⊕ A₁` spanned by the black nodes. The
  product did *not* resist: `mul_apply_eq_comp` to evaluate the product, `cartanReflection_simpleRoot`
  for `s_j α_i = α_i - a_{ij} α_j`, then `cartanReflection_simpleRoot_self`. (Upstream note:
  `LinearEquiv.mul_apply` is deprecated in favour of `mul_apply_eq_comp` at this pin, which is what
  the proof uses.)

In the probe the longest element is the product of the two reflection *equivalences*
(`cartanReflectionEquiv A 0 * cartanReflectionEquiv A 2`), which is in `W_X` by
`Subgroup.mul_mem`; condition (2) then holds with `-w_X = id` on `X` and `τ = id`. Condition (3) is
the one the source computes: with `ρ^∨_X = (h₁ + h₃)/2`, `α₁(ρ^∨_X) = α₃(ρ^∨_X) = 1` (no white
`τ`-fixed node there) and `α₂(ρ^∨_X) = -1 ∈ ℤ` at the `τ`-fixed white node `2`, witnessed by
`z = -1` in the `HasIntegralParabolicWeylPairing` field. The finite-type field is
`isFiniteTypeSubdiagram_pair` (`:418`) with `a_{11} = a_{33} = 2` and `a_{13} = a_{31} = 0`.

## 2. Item 2 — real forms: LANDED

`RealFormData.lean:56`:

```lean
structure RealForm (L : Type u) [LieRing L] [LieAlgebra ℂ L] where
  carrier : Type u
  [lieRing : LieRing carrier]
  [lieAlgebra : LieAlgebra ℝ carrier]
  extension : ℂ ⊗[ℝ] carrier ≃ₗ⁅ℂ⁆ L
```

`ℂ ⊗[ℝ] carrier ≃ₗ⁅ℂ⁆ L` is `g₀ ⊗_ℝ ℂ ≅ g` in Mathlib's orientation
(`LieAlgebra.ExtendScalars`; `TensorProduct.comm` converts). Supporting declarations:

| line | declaration | content |
| --- | --- | --- |
| 71 | `RealForm.copy F v` | the image of `v` under `v ↦ 1 ⊗ v`, i.e. `g₀` inside `g` |
| 82 | `RealForm.IsIsomorphic F G` | `∃ φ : F.carrier ≃ₗ⁅ℝ⁆ G.carrier, ∀ v, G.copy (φ v) = F.copy v` |
| 85, 88, 95 | `isIsomorphic_refl/_symm/_trans` | it is an equivalence relation |
| 104, 109 | `isoSetoid`, `Class` | isomorphism classes of real forms |
| 114 | `RealForm.ofScalarExtension V` | the definition is inhabited: the tautological real form of `ℂ ⊗[ℝ] V` |
| 136 | `bracket_copy_ofScalarExtension` | `⁅1 ⊗ v, 1 ⊗ w⁆ = 1 ⊗ ⁅v, w⁆` — the computation making `g₀` a *Lie* subalgebra |

The last one is the smallest input on which the definition's Lie-algebra content is decidable, and
it is the reason `lieSubalgebra` would be a `LieSubalgebra` rather than a subspace. The classical
presentation — `g₀` as the real Lie subalgebra `{v ↦ 1 ⊗ v}` of `g` — needs `LieAlgebra ℝ` on the
restriction of scalars `RestrictScalars ℝ ℂ L`; `LieAlgebra.RestrictScalars.lieAlgebra` exists but
`RestrictScalars ℝ ℂ L` is a `def` synonym that Lean's default transparency does not unify with `L`,
so every membership proof needs `RestrictScalars.addEquiv ℝ ℂ L` inserted by hand. `RealForm.IsIsomorphic`
is therefore stated through the embeddings instead, which is where the differential is recorded
(`RealForm.IsIsomorphic` docstring, and `COMPLAINTS.md`). This is a *presentation* difference, not a
weakening of what a real form is: the two agree whenever the embeddings generate `L`, which holds
for a real form of a semisimple `L`.

## 3. Item 3 — Araki's classification: NOT LANDED (statement only)

Landed: the statement, in the corrected form of the audit comment on this issue.

`RealFormData.lean:199` — `RealFormCorrespondence A L`: `toRealForm : (X) (τ) → IsAdmissiblePair A X τ
→ RealForm L`, plus

```lean
  injective : ∀ (X) (τ) (h) (X') (τ') (h'),
    (toRealForm X τ h).IsIsomorphic (toRealForm X' τ' h') → SameDiagramOrbit A (X, τ) (X', τ')
  surjective : ∀ F : RealForm L, ∃ (X) (τ) (h), F.IsIsomorphic (toRealForm X τ h)
```

and `RealFormData.lean:213` — `def ArakiClassification (A) (L) : Prop := ∃ _ : RealFormCorrespondence A L, True`.
That is a `Prop`-valued *definition*: nothing asserts it. The diagram side is the `Aut(A)`-orbit
relation `SameDiagramOrbit` (`:162`), not equality of pairs, which is exactly the audit's correction.

The correction itself has provable content, and it landed:

| line | declaration | content |
| --- | --- | --- |
| 147 | `diagramAutomorphismGroup A ≤ Equiv.Perm ι` | `Aut(A)` is a group (`hσ (τ i) (τ j)`, `isDiagramAutomorphism_inv`) |
| 166 | `diagramTriality : Equiv.Perm (Fin 4)` | `Equiv.swap 0 2 * Equiv.swap 2 3`, a 3-cycle of the `D₄` leaves |
| 169 | `diagramTriality_mem` | triality lies in `Aut(D₄)` |
| 173 | `diagramTriality_apply_zero` | it sends node `0` to node `2` |
| 181 | `diagramTriality_not_preserves` | `¬ PreservesSubdiagram diagramTriality {0}` |

The last theorem is the mechanism: an `Aut(A)`-element need not preserve a black-node set, so
`Aut(A)`-orbits are coarser than isomorphism classes of objects of `SatakeDiagram`, and a
classification that named the pairs themselves would be false — which is the audit's point
(`so(6,2)` and `so*(8)` in `D₄`).

What resists, exactly:

* **Direction "pair ↦ real form".** The construction is Kolb's `θ(X, τ) = Ad(s(X, τ)) ◦ τ ◦ ω ◦
  Ad(m_X)` (Theorem 2.5, arXiv:1207.6036v2, p. 10), an automorphism of a Kac–Moody algebra `g(A)`
  of the second kind. This repository has no `g(A)`; Mathlib has `RootPairing`
  (`LinearAlgebra/RootSystem/Defs.lean:80`) and `RootPairing.Base.cartanMatrix`
  (`LinearAlgebra/RootSystem/CartanMatrix.lean:106`) but no Chevalley–Serre construction of a Lie
  algebra from a root datum, and `Algebra/Lie/CartanExists.lean` does not extract a Dynkin diagram
  from a semisimple Lie algebra.
* **Direction "real form ↦ pair".** Needs the Cartan involution of a real form and the Satake
  diagram of a symmetric pair, neither of which exists in Mathlib at the pinned revision.
* **The quotient is not yet a quotient.** `SameDiagramOrbit` is a relation on
  `Finset ι × Equiv.Perm ι`; that it descends to the admissible pairs needs the transport of the
  four conditions along `σ ∈ Aut(A)`, which is not written. All four transports are identified and
  costed in `COMPLAINTS.md` (`#86 — the Aut(A)-action on admissible pairs is not proved well defined`).

So the acceptance for item 3 is met in the only form that does not assert unproved mathematics: the
statement, with the correction inside it, plus the diagram-side content that is provable. The
missing existence theorem is in `COMPLAINTS.md`, not silently dropped.

## What was searched (LC-09), and where

Before each definition:

* `python3 scripts/formalization_corpus.py search "Satake"` — 15 files, all Satake *parameters* of
  modular forms (TauCeti `NumberTheory/ModularForms/Newforms/Satake.lean`) etc.; no diagram.
* `… search "SatakeDiagram"` — 0 files.
* `… search "realForm"` — 7 files, two machine-learning hits (`QudeLeap__Lean-QuantumAlg`
  `dlaRealForm`) and no classification.
* `… search "admissible pair"`, `… "restricted root"` — no relevant hits (zkEVM `Admissible.lean`
  is about suprema; a Kolmogorov-complexity file).
* `rg -il "satake" LeanCategories` → `K3SBBoundaryData.lean` only (a Satake compactification
  docstring); `rg -il "realform|real form"` → quadratic-form uses only.
* Mathlib at the pinned revision: `Matrix.Cartan` was deprecated into
  `LinearAlgebra/Matrix/Cartan/{Basic,Realisation}.lean`; `CartanMatrix.{A,B,D,E₆,…,G₂}` are the
  matrices used in the probes; `RootPairing`, `RootPairing.Base.cartanMatrix`,
  `RootPairing.Base.equivOfCartanMatrixEq` (`CartanMatrix.lean:361`), `LieAlgebra.ExtendScalars`
  (`Algebra/Lie/BaseChange.lean`), `LieAlgebra.IsSemisimple`
  (`Algebra/Lie/Semisimple/Defs.lean:105`).

## The whole-library gate

Run on HEAD `f8ab14d1` plus this turn's three files (`SatakeDiagramData.lean`,
`RealFormData.lean`, this report); `git status` showed no other tracked modification and no other
chat's `lake`/`lean` process was running when it started. Nothing was decompressed: `cache-get`
reported "every entry is named by some worktree's manifest" and every package tree already linked.

```
lake build LeanCategories.All
  → Build completed successfully (20072 jobs)

just test                     (exit 0, 13 min 11 s)
  build                       → cache-get: all trees linked, nothing fetched
                                Build completed successfully (8342 jobs)
                                build-timing: 0 timed module jobs
                                  -> build-timings/f8ab14d1077d-20261118T013141Z.tsv
  lean-no-sorry               → "No sorry declarations in tracked Lean sources."
  _lean-vacuity-audit         → LeanCategories.Tools.VacuityAudit built (27 s);
                                Build completed successfully (20074 jobs);
                                no `noBareNonempty` finding
  _lean-mathlib-lint-audit    → 13 `#lint only` lines (checkType, defsWithUnderscore,
                                deprecatedNoSince, impossibleInstance, noBareNonempty,
                                nonClassInstance, simpComm, simpNF, structureInType,
                                subsetDotNotationLinter, synTaut, tacticDocs,
                                unusedHavesSuffices): each
                                "Found 0 errors in 18026 declarations (plus 11753
                                automatically generated ones)", "All linting checks
                                passed!"
  _lean-unused-variables      → passed (no `linter.unusedVariables` finding)
  _lean-axiom-audit           → LeanCategories.Tools.AxiomAudit (359 s) and
                                AxiomAuditMain built; no declaration outside
                                [propext, Classical.choice, Quot.sound]
df after: 9.6 G free on /
```

The **first** run of `just test` was red, on this issue's own file, and the fix is part of this
turn's diff: the `synTaut` linter reported
`LeanCategories.Algebra.RealForm.class_ofScalarExtension /- LHS equals RHS syntactically -/` — a
theorem stated as `q = q`, so worthless. It is replaced by an inhabitant of the class type,

```lean
def classOfScalarExtension (V : Type u) [LieRing V] [LieAlgebra ℝ V] : Class (ℂ ⊗[ℝ] V) :=
  Quotient.mk (isoSetoid (ℂ ⊗[ℝ] V)) (ofScalarExtension V)
```

(`RealFormData.lean:121`). In that first run the build, `lean-no-sorry` and the vacuity audit had
already passed; the lint audit aborted the recipe, so `_lean-unused-variables` and
`_lean-axiom-audit` were not reached until the second run above.

Pre-existing gate noise seen in the log and not touched, since it is not this issue's: the
`Tools/AxiomAudit.lean:15` long line, the ambiguous-namespace warnings in
`ForMathlib/GrothendieckCocartesian.lean`, `Topology/Cards/*` and
`Lattices/Valued/PadicMixedSymbol.lean`, and the unscoped `maxHeartbeats` warning in
`ForMathlib/CategoricalPullback.lean:30`.

## Environment note

`lean` on `PATH` resolves to the `elan` toolchain pinned by `lean-toolchain` (v4.36.0), while
`/opt/mathlib` is a v4.33.1 build, so a bare `lean` fails with `Init.olean ... incompatible header`;
`lake env lean` in this worktree works and is what every check above used.

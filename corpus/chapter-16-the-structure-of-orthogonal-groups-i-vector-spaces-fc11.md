---
type: reference
title: "Chapter 16. The Structure of Orthogonal Groups I, Vector Spaces FC11"
description: "# Chapter 16. The Structure of Orthogonal Groups I, Vector Spaces FC11"
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
# Chapter 16. The Structure of Orthogonal Groups I, Vector Spaces FC11

## Chapter 16. The Structure of Orthogonal Groups I, Vector Spaces

### FC11-C16-U007 continuation, 2026-09-22

`LeanCategories/Modules/Quadratic/Orientation.lean` now defines
`PositiveOrientationFamily`, `IsCoherentPositiveOrientation`,
`PositiveOrientation`, and `NegativeOrientation`, using native orientations,
`sigPos`, and the orthogonal-projection equation. No transport framework or
theorem proof is introduced. The focused Lean 4.33.0 check passed in 14.91s.
Original-text acceptance was completed later on 2026-09-22 against the
author's Version JUNE 2024 PDF, printed pp. 293--294. Its exact download
URL and SHA-256 are recorded in `provenance-contract-for-fc11-c09.md`.
The source asks for orientations on every maximal positive-definite
subspace, not just one supplied subspace, with the negative version obtained
by changing the sign of the form. `PositiveOrientationFamily` retains that
whole family and the exact maximal dimension `sigPos Q`.
`IsCoherentPositiveOrientation` expresses compatibility using the
`Q`-orthogonal-projection equation and native `Orientation.map`, rather
than arbitrary supplied comparison maps. `PositiveOrientation` is the
subtype satisfying this predicate; `NegativeOrientation` applies it to
`-Q`. The source specialization is a finite-dimensional indefinite real
inner-product space. Existence of projection equivalences, extension of
one chosen orientation, and the connected-component and spinor-norm
comparisons are results, not additional Sweep-III obligations. No source
code changed since the successful check at `3187664`, so that check is
reused rather than rerun. No aggregate export is changed here.

| FC11 ID | Verdict | Route | Lean target(s) | Provenance | Interface comparison |
| --- | --- | --- | --- | --- | --- |
| `FC11-C16-U001` | rotations/reflections and the hyperplane-reflection formula are direct linear algebra | `mathlib` | `Mathlib/LinearAlgebra/Reflection.lean::Module.reflection`, `Module.reflection_apply`; `Mathlib/LinearAlgebra/RootSystem/OfBilinear.lean::LinearMap.IsReflective.isOrthogonal_reflection`; `LinearEquiv.det`; diagonal quadratic map `x ↦ (2:ℝ)⁻¹ * b x x` | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d | For anisotropic `x`, take the linear functional `v ↦ b(x,v)/q(x)`; it evaluates to `2` on `x`, so `Module.reflection` is exactly `v ↦ v - b(x,v)/q(x) • x`, and the bilinear-form reflection theorem gives orthogonality. Rotation/reflection terminology is then the determinant `±1` predicate. The project reflection wrappers are unnecessary as routes. |
| `FC11-C16-U002` | reduced real orthogonal group is implemented as the kernel of the canonical spinor norm, with the implementation route exposed | `project-existing` | `LeanCategories/Lattices/Valued/CanonicalSpinorNorm.lean::canonicalSpinorNorm`; route: `SpinorNormDescent.lean::spinorNormOfNondegenerate` factors `SpinorNormConstruction.lean::lipschitzSpinorNorm` through `lipschitzActionHom` by `MonoidHom.liftOfSurjective`; Mathlib `CliffordAlgebra`, `lipschitzGroup`, `QuotientGroup`/square classes, `MonoidHom.ker`; project `ReflectionGeneration.lean::reflectionsGenerate` proves uniqueness | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; implementation literature provenance: Cassels, *Rational Quadratic Forms*, Ch. 10 §3, recorded in `SpinorNormDescent.lean` | This is genuine prior project mathematics rather than a wrapper over an upstream declaration: the project constructs the Clifford/Lipschitz norm, proves descent through the orthogonal action, and obtains the canonical homomorphism to square classes. Specializing to `ℝ` and taking its kernel is exactly the source reduced orthogonal group. |
| `FC11-C16-U003` | signed-spinor reflection lemma remains absent | `unmatched` | partial: U001 reflection; U002 ordinary spinor norm; real sign/square-class arithmetic | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | No checked signed-spinor homomorphism with the source `ε` normalization exists, so the claimed value on a reflection of prescribed sign is not yet a theorem. |
| `FC11-C16-U004` | signed spinor norms and their kernel subgroups are direct from the real square-class spinor norm and determinant | `project-existing` | `LeanCategories/Lattices/Valued/CanonicalSpinorNorm.lean::canonicalSpinorNorm`; real square classes `ℝˣ/(ℝˣ)² ≃ {±1}`; `LinearEquiv.det`; generic product of homomorphisms and `MonoidHom.ker` | remap 2026-09-16; P=db584cd6d46c92f209a44c0f1c829460d327499d; source-sign convention audit plus live corpus search `signed spinor norm real orthogonal orientation` (no more specialized owner) | The positive signed norm is the sign of the ordinary real spinor square class. Negating the quadratic form multiplies each reflection value by `-1`; since a product of `r` reflections has determinant `(-1)^r`, the negative signed norm is `det · Nm_spin^+`. Thus both homomorphisms and `O^ε(V)=ker(Nm_spin^ε)` assemble canonically from existing maps. U005 records their comparison properties rather than defining extra data. |
| `FC11-C16-U005` | signed-spinor comparison/definite-form conventions remain absent | `unmatched` | partial: ordinary spinor norm, opposite/scaled forms and real signature | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | No checked signed-spinor package proves agreement for `ε=+`, triviality on `ε`-definite forms, or interchange under negating the quadratic form. |
| `FC11-C16-U006` | sign-structure definition is direct orientation plus maximal definite subspace data | `mathlib` | `Mathlib/LinearAlgebra/Orientation.lean::Orientation`, `Orientation.map`; `Mathlib/LinearAlgebra/QuadraticForm/Basic.lean::QuadraticMap.PosDef`; `Mathlib/LinearAlgebra/QuadraticForm/Signature.lean::QuadraticForm.sigPos_isGreatest`, `sigNeg_isGreatest`, `exists_finrank_eq_sigPos_and_posDef`, `exists_finrank_eq_sigNeg_and_negDef`; `QuadraticMap.restrict` | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d | A positive sign structure is an orientation on a subspace realizing the maximal positive dimension `sigPos`; the negative version uses `sigNeg` and `(-Q).restrict`. Mathlib supplies both the orientations and the maximal-definite-subspace characterization, so no project signature wrapper is needed. |
| `FC11-C16-U007` | `[definition-only] [negative-search-complete] [residue-search-audited] [realized]` coherent maximal-definite-subspace orientation data at the existing quadratic-form owner | unmatched | local `LeanCategories/Modules/Quadratic/Orientation.lean::LeanCategories.Modules.Quadratic.{PositiveOrientationFamily,IsCoherentPositiveOrientation,PositiveOrientation,NegativeOrientation}`; native `Orientation`, `Orientation.map`, `sigPos`, `QuadraticForm.restrict` and `QuadraticForm.IsOrtho` | Final open-ended audit 2026-09-18; source implementation and successful focused Lean 4.33.0 check at `3187664` (14.91s); original June-2024 author PDF, printed pp. 293--294, compared on 2026-09-22 | The family ranges over all subspaces of dimension `sigPos Q` on which the restricted form is positive definite. Its coherence predicate requires native orientation transport along every equivalence satisfying the `Q`-orthogonal-projection equation. A positive orientation is that coherent-family subtype, and a negative orientation is the same definition for `-Q`. No arbitrary transport system or proof of its existence is supplied. Extension from one fiber, topological comparisons and the orthogonal-group component results remain Sweep IV. |
| `FC11-C16-U008` | four-component orthogonal-group comparison remains absent | `unmatched` | partial: determinant, ordinary spinor norm, U006/U007 sign structures and topological group infrastructure | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | No checked theorem classifies connected components of `O(n₊,n₋)` by determinant and signed spinor norm or proves the stated orientation interpretation. |
| `FC11-C16-U009` | connected-component/signed-spinor orientation theorem remains absent | `unmatched` | partial: U004/U007/U008 | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | This is the precise real-orthogonal component classification missing from the current topology/spinor API. |
| `FC11-C16-U010` | hyperbolic/Lorentzian vector-space terminology is a direct signature predicate | `mathlib` | `Mathlib/LinearAlgebra/QuadraticForm/Signature.lean::QuadraticForm.sigPos`, `sigNeg`, `sigPos_add_sigNeg_add_radical`; weighted-sum-of-squares/signature classification; finite-dimensional real quadratic forms | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d | The displayed Minkowski form has nondegenerate real signature with one distinguished sign, i.e. `min (sigPos Q) (sigNeg Q) = 1` and zero radical. This is the same direct signature predicate already routed in `FC11-C04-U008`; the project `IsLorentzianSignature` name is only convenience packaging. |
| `FC11-C16-U011` | light-cone two-component/convexity theorem remains absent | `unmatched` | partial: U010 Lorentzian signature; generic real topology, convexity and bilinear forms | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | No checked Lorentzian linear-algebra theorem constructs the two convex time-cone components and proves the stated inner-product sign criteria, including the closure clause. |
| `FC11-C16-U012` | [definition-only] O⁻(V) is the direct setwise stabilizer of the chosen light-cone component | `mathlib` | mapped Lorentzian space `FC11-C16-U010`; chosen subset `C_V`; orthogonal group action on `V`; generic setwise stabilizer `MulAction.stabilizer`/`Subgroup`; mapped orientation data `FC11-C16-U006` | remap 2026-09-16; P=db584cd6d46c92f209a44c0f1c829460d327499d | Once the preceding source theorem supplies or chooses one light-cone component `C_V`, the displayed subgroup `{g | g(C_V)=C_V}` is exactly the ordinary setwise stabilizer and needs no new orthogonal-group machinery. The equivalence with preservation of the corresponding positive-line orientation is theorem content and remains for Sweep IV. |
| `FC11-C16-U013` | Dickson invariant formula is a direct finite matrix/sum expression | `mathlib` | `Mathlib/LinearAlgebra/SymplecticGroup.lean::symplecticGroup`; matrices, block entries, finite sums and field arithmetic; quadratic-form coefficients relative to a basis | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | Definition 16.2.1 is literally the displayed polynomial expression in matrix and quadratic-form coordinates, all of which are native Mathlib data. No local wrapper is mathematically necessary. |
| `FC11-C16-U014` | Dickson invariant takes values zero/one on the orthogonal group remains absent | `unmatched` | partial: U013 explicit formula; orthogonal/symplectic matrix predicates | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | No checked characteristic-two theorem proves the formula restricts to `{0,1}` on `O(q)`. |
| `FC11-C16-U015` | characteristic-two transvection/reflection Dickson computation remains absent | `unmatched` | partial: generic transvections, U013 formula; symplectic group | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | No checked theorem proves the exact orthogonality criterion `q(u)=a⁻¹` and Dickson value one for the source transvection. |
| `FC11-C16-U016` | Dickson cocycle/additive-homomorphism theorem remains absent | `unmatched` | partial: U013 formula; matrix multiplication/symplectic group | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | No checked theorem proves the cocycle identity or its additive restriction to the orthogonal group. |
| `FC11-C16-U017` | rotation subgroup in characteristic two is the direct zero fiber once Dickson is available | `mathlib` | U013 direct Dickson expression; generic `Function` fiber, additive hom kernel and subgroup/index-two constructions | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | The source definition is simply the kernel/zero fiber of the Dickson invariant on `O(q)`. The theorem that this expression is a homomorphism/index two is U016, not part of the defining predicate. |
| `FC11-C16-U018` | characteristic-two rotation predicate is the Dickson-zero predicate | `mathlib` | U013 direct Dickson expression and orthogonal transformation predicate | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | A rotation is by definition an orthogonal transformation whose Dickson expression equals zero; this needs no new mathematical object beyond U013. |
| `FC11-C16-U019` | even products of reflections are rotations remains dependent on missing Dickson reflection/cocycle theorems | `unmatched` | partial: U015 reflection value one; U016 additivity | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | The conclusion follows formally from U015/U016, but those characteristic-two Dickson results are not checked. |
| `FC11-C16-U020` | hyperbolic-plane Dickson classification example remains source-specific | `unmatched` | partial: mapped `FC11-C06-U060`; U013 Dickson formula | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | No checked declaration computes the Dickson values of the `i_a,j_b` families or proves every rotation is a product of two reflections in this example. |
| `FC11-C16-U021` | exceptional binary `F₂` quadratic-space Dickson classification remains absent | `unmatched` | partial: finite-field quadratic forms and U013 formula | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | No checked theorem classifies the orthogonal transformations of the norm form of `F₄/F₂` and their Dickson values. |
| `FC11-C16-U022` | `s₀/s₁` counting notation is native finite-set cardinality | `mathlib` | `Finset.univ.filter`, `Fintype.card`, fibers of a quadratic form over `F₂` | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | The source values are just the cardinalities of vectors on which the quadratic form takes `0` or `1`; these are direct finite-set expressions. |
| FC11-C16-U023 | democratic Arf invariant on finite nondegenerate polar forms [realized] | reference-port | `roed-math/gq2-lean::GQ2/QuadraticFp2.lean::{zeroCount,arf}`; `arf q := if 2 * zeroCount q > Nat.card V then 0 else 1`; U022 source count notation; local `LeanCategories/ForMathlib/DemocraticArfInvariant.lean::LeanCategories.ForMathlib.QuadraticMap.{zeroCount,democraticArfInvariant}` | formalization-corpus snapshot `roed-math/gq2-lean@3c7b1abaf04ec8424decc2b1eb1b91bfe0ce5a33` indexed 2026-09-15; refreshed exact search 2026-09-16; Apache-2.0; focused Lean elaboration passed 2026-09-19 | Peters–Sterk §16.3, Table 16.3.2, defines the majority value for type-I/type-II quadratic spaces over F₂. The port uses the exact reference count formula, with finite V and the explicit premise q.polarBilin.Nondegenerate. The zero vector is included in the count. Type III in the surrounding section has tied fibers and is excluded by this premise. Thus this source specialization does not silently assign an Arf invariant to a tied semi-unimodular space. No comparison with a separate Arf-class construction or counting theorem is claimed. |
| `FC11-C16-U024` | `[definition-only] [realized]` compact-complex-curve divisors, support, degree, nonzero rational-function representative data, principal-divisor and linear-equivalence predicates are ported at the no-proof boundary | `reference-port` | pinned reference `mrdouglasny/jacobian-challenge@8ce1ec28aed1c78b3b39d0bae26e2858c82f5143::{Jacobians/RiemannSurface/Divisor.lean,Jacobians/RiemannSurface/MeromorphicFunctionField.lean}`; local adaptation `LeanCategories/Algebra/RiemannSurfaceDivisorData.lean::{LeanCategories.Algebra.curveMeromorphicAtData,curveOrderAtData,NonzeroCurveRationalFunctionData,CurveDivisorData,curveDivisorSupportData,curveDivisorDegreeData,IsCurvePrincipalDivisorData,CurveDivisorData.IsPrincipalData,CurveDivisorData.LinearlyEquivalentData}` | C=8ce1ec28aed1c78b3b39d0bae26e2858c82f5143; Apache-2.0; repaired for the current no-proof boundary 2026-09-23; focused `lake build LeanCategories.Algebra.RiemannSurfaceDivisorData` green | The local carrier is exactly the source free abelian group on curve points; support is its finite `Finsupp` support and degree is the coefficient-sum homomorphism. Principal and linearly equivalent divisors are now stated relationally by the coefficient equation `coeff_p(D)=ord_p(f)`; no finite divisor, principal subgroup, or Picard quotient is selected before the finite-support/additivity results exist. Finite support of the order function, existence/uniqueness of `div(f)`, additivity, degree zero, and equivalence/subgroup laws remain result content. |
| `FC11-C16-U025` | `[definition-only] [realized]` rational-function evaluation on divisors is the source's literal finite complex product over divisor support; nonvanishing, unit-valuedness, functoriality and Weil reciprocity remain result content | `reference-port` | pinned reference `mrdouglasny/jacobian-challenge@8ce1ec28aed1c78b3b39d0bae26e2858c82f5143` supplies the U024 free-abelian divisor and meromorphic/order infrastructure but has no packaged divisor-evaluation declaration; local adaptation `LeanCategories/Algebra/RiemannSurfaceDivisorEvaluationData.lean::{LeanCategories.Algebra.curveRationalFunctionSupportData,CurveDivisorEvaluationAdmissibleData,curveDivisorEvaluationComplexData}`; native finite products and integer powers | C=8ce1ec28aed1c78b3b39d0bae26e2858c82f5143; Apache-2.0; repaired for the current no-proof boundary 2026-09-23; focused `lake build LeanCategories.Algebra.RiemannSurfaceDivisorEvaluationData` green | `CurveDivisorEvaluationAdmissibleData` is disjointness of the zero/pole locus from `supp(D)`, and `curveDivisorEvaluationComplexData` is literally `∏_{x∈supp D} f(x)^{n_x}` using the rational-function representative's point value. No regular-value or complex-unit witness is selected by choice. The theorem that the product is independent of representative and nonzero under the source hypothesis, hence lies in `ℂˣ`, remains Sweep-IV content. |
| `FC11-C16-U026` | `[definition-only] [realized]` the holomorphic-form dual, analytic arc integral, first-homology carrier, exact candidate-period relation, and raw quotient `H⁰(C,Ω¹)^*/ι(H₁(C,ℤ))` are transcribed locally; period linearity/additivity and quotient-group/torus structure remain result-layer | `reference-port` | local `LeanCategories/Algebra/RiemannSurface{JacobianData,PeriodIntegralData,HomologyPeriodData,JacobianQuotientData}.lean::{CurveHolomorphicOneFormData,CurveJacobianDualData,curveCanonicalArcIntegralData,CurveIntegralFirstHomologyData,IsCurveHomologyPeriodFunctionalData,curveIntegralPeriodCandidateSetData,IsCurveIntegralPeriodSubgroupData,CurveIntegralPeriodRelationData,CurveJacobianQuotientData,curveJacobianClassData}`; reference `mrdouglasny/jacobian-challenge@8ce1ec28aed1c78b3b39d0bae26e2858c82f5143` | Reference Apache-2.0, Lean 4.30.0; no-proof audit 2026-09-23 removed epsilon-selected period functionals/subgroups; State-2 representation repair 2026-09-25 forms the source quotient as raw `Quot` on the exact candidate-period difference relation; focused `lake env lean LeanCategories/Algebra/RiemannSurfaceJacobianQuotientData.lean` green | No period functional, subgroup, or quotient operation is chosen by epsilon. The local relation says exactly that two dual functionals differ by a candidate integral period; raw `Quot` needs no proof that this relation is already an equivalence relation. Once Sweep IV proves existence/uniqueness/additivity of the period functional, the candidate set is the image `ι(H₁(C,ℤ))` and the relation is the ordinary coset relation. Group structure, lattice discreteness, complex-torus structure, and projectivity remain result content. |
| `FC11-C16-U027` | `[definition-only] [realized]` Riemann theta lattice series transcribed locally from the source formula; convergence, holomorphy, quasi-periodicity, and theta-divisor comparisons remain result content | `reference-port` | local `LeanCategories/Algebra/RiemannTheta.lean::{LeanCategories.Algebra.riemannThetaSummand,riemannTheta}`; reference `mrdouglasny/jacobian-challenge@8ce1ec28aed1c78b3b39d0bae26e2858c82f5143::Jacobians/AbelianVariety/Theta.lean::{thetaSummand,RiemannTheta}`; native `Matrix.mulVec`, `Matrix.dotProduct`, `Complex.exp`, `tsum` | C=8ce1ec28aed1c78b3b39d0bae26e2858c82f5143; Apache-2.0; local source transcription 2026-09-19; target-pin acceptance 2026-09-23: focused `lake env lean LeanCategories/Algebra/RiemannTheta.lean` green after importing the `Real.pi` owner and using the pinned `dotProduct` name | `riemannTheta Z z` is exactly the displayed sum over `x : ℤ^g` of `exp(2πi · x·(z + 1/2 Zx))`. The definition uses total `tsum`, so no convergence proof is smuggled into the constructor. The source's everywhere convergence, holomorphy/quasi-periodicity, and divisor consequences remain Sweep-IV result clauses. |
| `FC11-C16-U028` | theta-with-characteristics identities remain absent | `unmatched` | partial: U027 theta series target; complex exponential arithmetic | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | No checked theorem proves the translation, integral-characteristic invariance, or parity identity of Riemann theta functions. |
| `FC11-C16-U029` | `[definition-only] [realized]` the Abel--Jacobi construction is transcribed as the exact graph relating `x` to the raw Jacobian class of a path-integral functional from `x₀` to `x`; existence, path independence, uniqueness, and functionality remain result-layer | `reference-port` | `mrdouglasny/jacobian-challenge@8ce1ec28aed1c78b3b39d0bae26e2858c82f5143::Jacobians/Axioms/AbelJacobiMap.lean::{pathIntegralBasepointFunctional,ofCurveAmbient,ofCurveImpl}`; local `LeanCategories/Algebra/RiemannSurfaceAbelJacobiData.lean::{CurveBasedAnalyticArcData,IsCurvePathIntegralFunctionalData,curvePathIntegralFunctionData,curveAbelJacobiLiftFunctionData,IsCurveAbelJacobiClassData,IsCurveAbelJacobiMapData}`; U026 raw Jacobian quotient | C=8ce1ec28aed1c78b3b39d0bae26e2858c82f5143; Apache-2.0; exact reference re-audited 2026-09-23; State-2 representation repair 2026-09-25 replaces the inadmissible selected linear functional by the source graph; focused `lake env lean LeanCategories/Algebra/RiemannSurfaceAbelJacobiData.lean` green | No dual-valued path integral or map is selected by epsilon. `IsCurveAbelJacobiClassData x₀ x q` says exactly that `q` has a dual-functional representative whose values are the source path integrals along an analytic arc from `x₀` to `x`; `IsCurveAbelJacobiMapData` is the graph predicate for a proposed function. Proving that the pointwise graph is inhabited and single-valued, and hence that the source map exists and is path-independent, is Sweep-IV result work. |
| `FC11-C16-U030` | `[definition-only] [realized]` the half-canonical predicate and the Riemann-constant graph `κ=α([θ₀])` are transcribed over certified canonical-divisor data and the raw Jacobian quotient; degree, existence, path independence, and divisor-class descent remain result-layer | `reference-port` | `Vilin97/lean-pool@3fc79f0a795f19fffcc59eee3efaf5faa52de3c3::RS.canonicalDivisorOf`; local `LeanCategories/Algebra/RiemannSurface{CanonicalDivisorData,ThetaCharacteristicData}.lean::{CurveCanonicalDivisorData,IsCurveThetaCharacteristicData,CurveThetaCharacteristicData,curveDivisorAbelJacobiLiftData,IsCurveDivisorAbelJacobiClassData,IsCurveRiemannConstantData}`; U029 Abel--Jacobi graph | no-proof audit 2026-09-23 removed epsilon-selected canonical divisors and the premature Riemann-constant value; State-2 representation repair 2026-09-25 adds the exact divisor-level Abel--Jacobi/Riemann-constant graph; focused `lake env lean LeanCategories/Algebra/RiemannSurfaceThetaCharacteristicData.lean` green | The half-canonical clause remains exactly `2θ ∼ K_C`, with `K_C` a certified divisor of a supplied nonzero holomorphic one-form. The divisor-level Abel--Jacobi graph sums pointwise path-integral dual functionals via the native free-abelian-group lift and takes their raw Jacobian class; `IsCurveRiemannConstantData` specializes this to `θ₀`. Existence and degree `g-1` of `θ₀`, degree `2g-2` of `K_C`, path independence, invariance under linear equivalence, and uniqueness of the resulting Riemann constant remain Sweep-IV results. |
| FC11-C16-U031 | `[sweep-iii-blocked]` parity is direct once the canonical Riemann--Roch submodule `L(θ)` exists, but the routed reference constructs that submodule using closure proofs | reference-port | LeanPool Riemann--Roch/linear-system dimension `RS.l`; local preparatory `LeanCategories/Algebra/RiemannSurface{LinearSystemData,ThetaParityData}.lean::{IsCurveLinearSystemData,CurveLinearSystemData,curveSectionDimensionData,CurveThetaCharacteristicData.IsEvenForLinearSystemData,CurveThetaCharacteristicData.IsOddForLinearSystemData}`; Mathlib `Even`/`Odd` | formalization-corpus snapshot `Vilin97/lean-pool@3fc79f0a795f19fffcc59eee3efaf5faa52de3c3`; no-proof audit 2026-09-23 removed epsilon-selected `L(D)`; focused linear-system and theta-parity owner builds green | The local data now parameterize a certified submodule with the exact source carrier and can state parity relative to it. Constructing the intrinsic `L(θ)` requires proving submodule closure/representative compatibility, so the source predicate “parity of `h⁰(C,θ)`” remains Sweep-IV blocked rather than being assigned an arbitrary selected subspace. Construction prerequisites: `FC11-C16-U030`. |
| `FC11-C16-U032` | two-torsion/translated-theta multiplicity theorem remains absent | `unmatched` | partial: generic 2-torsion of abelian groups; U026-U031 Jacobian/theta data missing | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | No checked period-coordinate description of `J₂(C)`, translated theta divisor, Riemann singularity theorem, or multiplicity=`h⁰` result exists. |
| `FC11-C16-U033` | theta-characteristic parity dot-product lemma remains absent | `unmatched` | partial: finite `F₂` dot product; U032 period-coordinate/theta multiplicity theory missing | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | The finite-field dot product is native, but no checked theorem identifies it with parity of theta characteristics. |
| `FC11-C16-U034` | genus-one theta-characteristic count remains absent as curve geometry | `unmatched` | partial: finite combinatorics and U031 parity target | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | The numerical `3/1` split is elementary after the parity classification, but no checked genus-one theta-characteristic correspondence supplies the objects being counted. |
| `FC11-C16-U035` | genus-three theta-characteristic/bitangent count remains absent | `unmatched` | partial: finite combinatorics and plane-curve/projective geometry; U031-U033 missing | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | No checked theorem counts `36/28` theta characteristics or identifies the 28 odd ones of a smooth plane quartic with its bitangents. |
| `FC11-C16-U036` | `[definition-only] [negative-search-complete] [residue-search-audited] [sweep-iii-blocked]` representative-level divisor/function data and the displayed quotient are transcribed locally, but descent to the Jacobian-torsion pairing remains result-layer work | unmatched | local `LeanCategories/Algebra/RiemannSurfaceWeilPairingData.lean::{LeanCategories.Algebra.CurveWeilPairingAdmissibleData,LeanCategories.Algebra.curveWeilPairingRepresentativeData}`; current Jacobian divisor/Abel--Jacobi scaffolding; generic divisor/function evaluation; no checked descended Jacobian Weil pairing | Final open-ended audit 2026-09-18; admitted Peters--Sterk Version JUNE 2024 PDF re-downloaded 2026-09-23 from the repository-recorded author URL with SHA-256 `5bc968dad21b0288f2b3d49612d94e750cd759724a16c8c25724c79410641a33`; §16.4.C compared directly; focused `lake env lean -M 1536 ... RiemannSurfaceWeilPairingData.lean` green in 23.6s on 2026-09-23 | The source pairing requires divisors representing torsion Jacobian points, rational functions with prescribed divisors, disjoint-support moving, function-on-divisor evaluation, and choice-independence. The local representative formula is exact, and the PDF separately places nonvanishing, root-of-unity image, and Weil-reciprocity consequences after that definition. The complete Jacobian-torsion construction remains unavailable because U026/U029 and the descent/choice-independence results are result-layer work. U036 therefore remains blocked at the no-proof boundary. Construction prerequisites: `FC11-C16-U026`. |
| `FC11-C16-U037` | Jacobian two-torsion as symplectic `F₂` space with theta quadratic refinements remains absent | `unmatched` | partial: Mathlib symplectic groups/forms and quadratic maps; U026/U031/U036 geometric bridge missing | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | The abstract algebra is expressible, but no checked theorem transports the general Jacobian Weil pairing and theta characteristics to this symplectic/quadratic-refinement structure. |
| `FC11-C16-U038` | affine action on quadratic refinements is direct quadratic-map/linear-form algebra | `mathlib` | `Mathlib/LinearAlgebra/QuadraticForm/Basic.lean::QuadraticMap.polarBilin`; linear forms; addition of quadratic maps; nondegenerate alternating form identifies vectors with linear functionals | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | For a fixed symplectic form `J`, adding the linear form `x ↦ J(x,v)` preserves the polar form, giving the stated action of `V` on the set of quadratic refinements. This is direct existing algebra. |
| `FC11-C16-U039` | difference-vector/torsor construction for quadratic refinements is direct linear algebra | `mathlib` | `QuadraticMap.polarBilin`; subtraction/addition of maps; nondegeneracy equivalence `V ≃ V*`; sum-type/vector-space constructions | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | Two refinements with the same polar form differ by a linear functional, hence by a unique vector via nondegeneracy of `J`; the affine-torsor addition rules are generic linear algebra. |
| `FC11-C16-U040` | Arf-invariant counting theorem remains absent | `unmatched` | partial: U022 value counts, U038/U039 refinement torsor; no Arf invariant owner | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | No checked theorem defines/classifies the Arf invariant and counts the two orbits of quadratic refinements by `2^(g-1)(2^g±1)`. |
| `FC11-C16-U041` | theta-characteristic count and Arf-parity correspondence remain absent | `unmatched` | partial: U031 theta parity, U037 refinement bridge, U040 count theorem | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | No checked general-curve theorem identifies theta-characteristic parity with Arf invariant or transfers the finite quadratic-form count to the curve. |
| `FC11-C16-U042` | Mumford geometric characteristic-not-two comparison remains literature-only | `unmatched` | partial: U041 target and algebraic-curve infrastructure | remap 2026-09-13; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=87befc843c2b3a1be12dfa7979aaff0851f50c603a | No checked formalization of Mumford’s geometric proof or its extension to all characteristics different from two was found. |

## U026 realization continuation — 2026-09-22

The local definition data now occupy four owners under `LeanCategories/Algebra/`:

- `RiemannSurfaceJacobianData.lean`: `CurveHolomorphicOneFormData` and
  `CurveJacobianDualData`, directly reusing native analytic cotangent sections
  and the complex module dual. The pinned `OneForm.lean`, lines 7–32, explicitly
  identifies this representation; no chart-cocycle submodule or closure proof
  is copied.
- `RiemannSurfacePeriodIntegralData.lean`: the pinned strong analytic-arc and
  loop data, subordinate chart partitions, segment integrals and their finite
  sum, and the moving-chart scalar integral. The intrinsic coefficient adapter
  uses native `mfderiv` and `NormedSpace.fromTangentSpace`. The exact analytic-arc
  and partition owners were located in the reference after native/project
  name searches, not authored as a new supporting framework.
- `RiemannSurfaceHomologyPeriodData.lean`: the reference's native abelianized
  fundamental-group carrier, analytic-loop path and homology-class maps, and
  `curveHomologyPeriodFunctionalData`. Its defining predicate specifies the
  integral on every analytic-loop representative of the supplied homology
  class; the functional is selected from that intrinsic equation.
- `RiemannSurfaceJacobianQuotientData.lean`: the actual range of that raw
  homology-period map, the subgroup selected by its exact image carrier,
  `CurveJacobianPeriodQuotientData`, the native additive quotient projection,
  and `CurveJacobianData` with the reference's chosen-basepoint convention.
  The earlier generated-loop quotient model has been replaced; no arbitrary
  period lattice, complex-linear span, or topological closure remains.

Reference provenance is `mrdouglasny/jacobian-challenge` at
`8ce1ec28aed1c78b3b39d0bae26e2858c82f5143`, Apache-2.0, including the exact
`Homology.H1`, `PeriodCycleBasis.loopToHomology`, `MultiChartIntegral`, and
`CanonicalArcIntegral` owners. All four focused `lake env lean` checks pass
on Lean 4.33.0 with Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
The only native-path constructor evidence is already carried by the loop data
or supplied by native continuous-map restriction; no new proof block is added.

The two `Classical.epsilon` selections record definitions, not their
specification theorems. Representability, integrability, independence,
linearity, subgroup closure, selection specifications and complex-torus
properties remain Sweep IV and must not become Sweep-III prerequisites.
U026 retains the causal `reference-port` route. Original-source acceptance
was completed later on 2026-09-22 against the author's June-2024 PDF,
printed p. 301, including the paragraph specifying the homology-to-dual
integration map. All four owners were read again clause by clause: the
cotangent-section numerator, scalar integrals, homology classes and period
equation, exact image-carrier selection, native quotient and class map
agree with that definition. The reference's chosen basepoint is presentation
data; its independence remains a result. The source is specialized to a
compact connected Riemann surface, without claiming torus properties for
the more general raw definitions. The source files have not changed since
the successful checks recorded with `409c5da`, so those checks were reused.
The definition row is now marked realized; no result clause is accepted.
The inherited staged/unstaged generated selectors and global import file were
left untouched rather than absorbing other workers' changes into this unit.

## U029 realization continuation — 2026-09-22

`LeanCategories/Algebra/RiemannSurfaceAbelJacobiData.lean` now defines the
arc-integral equation, the endpoint-constrained path-integral lift, its
basepoint normalization, and the Abel--Jacobi map into the existing period
quotient. `curveAbelJacobiMapData` keeps the homology basepoint explicit;
`curveAbelJacobiData` uses the compact-curve and fixed-homology-basepoint
convention of the pinned reference. No new supporting theory is introduced.

The exact reference is `Jacobians/Axioms/AbelJacobiMap.lean` at
`8ce1ec28aed1c78b3b39d0bae26e2858c82f5143` (Apache-2.0):
`pathIntegralBasepointFunctional` computes the existing scalar arc integral,
and lines 542–555 define `ofCurveAmbient` and `ofCurveImpl`, including the
subtraction of the lift at the basepoint. The local intrinsic dual replaces
basis coordinates, using the already ported U026 owners. The lift predicate
quantifies existentially over an arc with the required endpoints; requiring
all arcs to give the same dual vector would incorrectly remove period ambiguity.

The intended input is a compact connected Hausdorff complex curve with a
chosen Abel--Jacobi basepoint. A bare arbitrary functional or supplied lattice
is not an input. Integrals along different paths may differ by periods, and
no global primitive, path independence, selection specification, or holomorphy
is asserted. These remain result content, not Sweep-III prerequisites.

U029 retains its causal `reference-port` route and is not marked `[realized]`.
The pinned original Peters--Sterk extraction was checked and is absent on this
host, so complete original-prose acceptance remains open. After the shared
Lean slot became free, two bounded checks of the existing imported owner
`RiemannSurfaceJacobianQuotientData.lean` failed with
`lean::memory_exception: excessive memory consumption detected at 'interpreter'`,
first at a 768 MB cap and then at 1536 MB. Neither produced its `.olean`,
so the new Abel--Jacobi module was not reached. No further compiler attempt
was made; this is a resource-limited validation failure, not a passing check
or a Lean source diagnostic. `git diff --check` and the ordinary commit hook
passed for the explicit-path commit. The inherited staged selectors and
global imports remain untouched.

### Next definition input: U030 canonical-divisor owner

The next source-interface lookup located `RS.canonicalDivisorOf` at
`Vilin97/lean-pool@3fc79f0a795f19fffcc59eee3efaf5faa52de3c3`,
`LeanPool/JacobianDiffgeo/CanonicalForms/OneDimensional.lean`, lines 202–205.
It is the abbreviation `Θ₀.divisor` on the reference's meromorphic-one-form
carrier `RS.MForm`, with a chosen nonzero reference form in applications.
That carrier is not the holomorphic-section input used by the U026 owners.
The U030 port must therefore inspect and reuse/adapt the cited meromorphic
form's order/divisor construction rather than supply an arbitrary canonical
divisor or copy the surrounding one-dimensionality/Riemann--Roch proofs.
No new supporting interface has been authored by this lookup.

### U030: canonical divisor, theta characteristic, and Riemann-constant data

The 2026-09-22 continuation transcribes the complete declaration/formula
portion of the catalogue's U030 clause. The mathematical owners are:

- `RiemannSurfaceCanonicalDivisorData.lean`: the order of the existing
  holomorphic one-form's chart coefficient, the canonical-divisor coefficient
  predicate, its selection from an explicit nonzero form on a compact connected
  complex curve, and its class in the existing Picard carrier.
- `RiemannSurfaceAbelJacobiData.lean`: `curveDivisorAbelJacobiData`, the native
  free-abelian-group extension of the existing based point map. The divisor map
  belongs here, not in the theta-characteristic consumer.
- `RiemannSurfaceThetaCharacteristicData.lean`: the predicate `2θ ∼ K_C`, its
  divisor-representative subtype, and `curveRiemannConstantData` for the
  explicitly chosen half-canonical divisor and basepoint.

The support lookup read the pinned LeanPool
`CanonicalForms/{OneDimensional,Differential,Quotient}.lean` files at
`3fc79f0a795f19fffcc59eee3efaf5faa52de3c3` (Apache-2.0).
`RS.canonicalDivisorOf` is the divisor of its chosen reference form;
`MForm.ord` descends the meromorphic order of the chart coefficient.
`Differential.lean` identifies holomorphic forms as the special case with the
same coefficient transformation. For this source's holomorphic input, the
existing intrinsic `CurveHolomorphicOneFormData` and
`curveOneFormChartCoefficientData` therefore supply the needed data directly.
The implementation reuses native `meromorphicOrderAt`, `FreeAbelianGroup`, and
the prior divisor/Picard/Abel--Jacobi owners. It does not introduce another
meromorphic-form quotient, support theory, module structure, or supplied
canonical-divisor/Abel--Jacobi-map parameter.

Finite support, the selection specification, chart independence, degree
`2g - 2`, linear-equivalence independence, half-canonical existence, class
descent, and Riemann-constant translation identities remain results. No proof
of any of them has been introduced. The chosen nonzero holomorphic form is
an explicit source input, not a claim that one exists on every genus.

The pinned original Peters--Sterk extraction is still absent on this host.
Available host memory fell from 723 MB to 423 MB while the source was written;
no Lean process was started into that pressure. The Abel--Jacobi import
closure also retains its previously recorded memory-limited validation.
These sources are banked as **unverified**. U030 retains its causal
`reference-port` mapping without `[realized]`; original-text acceptance and
target-pin validation are still open, and no aggregate export is added.

The next U031 clause has been read: parity is `Even`/`Odd` applied to
`h⁰(C,θ)`. Its mapped owner is pinned LeanPool `RS.l`, not an arbitrary
dimension supplied by the caller. Inspect that linear-system owner before
introducing its parity consumer; the U030 definitions do not construct it.

### U031: Riemann--Roch space and theta-characteristic parity

The 2026-09-22 continuation resolved the mapped supporting input by reading
`LeanPool/JacobianDiffgeo/Meromorphic/LinearSystem.lean`, lines 60–106,
and `Meromorphic/GermSpace.lean`, lines 57–85, at the existing pinned
`3fc79f0a795f19fffcc59eee3efaf5faa52de3c3` revision (Apache-2.0,
Rado Kirov). `RS.LinSys D` is the submodule of meromorphic codiscrete germs
with `-D(p) ≤ ord_p(f)` at every point; `RS.l D` is its complex `finrank`.
The already inspected native `Filter.Germ`, `Filter.codiscrete`, their
module instances, and the local U024 chart-order/divisor owner supply the
supporting data. No new generic function field or germ algebra is required.

`RiemannSurfaceLinearSystemData.lean` combines the reference's meromorphic
germ membership and order bound in one carrier inside that native module,
selects the submodule by its exact carrier, and defines
`curveSectionDimensionData` as its `Module.finrank`. This retains the zero
germ through its `WithTop` order and identifies representatives differing
at isolated points; it does not count arbitrary pointwise values as extra
sections. The sign of the bound is `-D(p)`, permitting the poles allowed by
an effective divisor rather than forcing additional zeros.

`RiemannSurfaceThetaParityData.lean` defines
`CurveThetaCharacteristicData.IsEvenData` and `.IsOddData` on the existing
half-canonical divisor subtype, using the constructed section dimension.
Closure, representative independence, the selection specification,
finite dimensionality, divisor-class invariance, theta multiplicity and
theta-characteristic counting remain Sweep-IV results. No proofs are added.

Both owners remain unverified. The focused command
`timeout --signal=TERM --kill-after=5s 75s lake env lean -M 1024 -o <scratch-olean> LeanCategories/Algebra/RiemannSurfaceLinearSystemData.lean`
exited 134 during import loading with
`lean::memory_exception: excessive memory consumption detected at 'interpreter'`.
There was no Lean source diagnostic and no successful `.olean` output.
The host had 1236 MB available before the single Lean process started.
No larger-cap retry or dependent parity compilation was launched; the
previously unverified U030/Abel--Jacobi import closure remains unchanged.
`git diff --check` passed. U031 retains its `reference-port` route without a
realization marker; the original June-2024 extraction is still absent.

### U036: divisor-representative Weil-pairing formula

The 2026-09-22 continuation transcribes the defining quotient from source
lines 8291--8295 in
`LeanCategories/Algebra/RiemannSurfaceWeilPairingData.lean`.
`CurveWeilPairingAdmissibleData` records the two degree-zero divisors,
disjoint divisor supports, the exact coefficient predicates
`div(f₁) = k D₁` and `div(f₂) = k D₂` for chosen nonzero rational functions,
and the two cross-evaluation admissibility conditions. The source derives
those cross-support conditions from the preceding data; Sweep III carries
them explicitly rather than importing that proof. The raw
`curveWeilPairingRepresentativeData` computes `f₁(D₂) / f₂(D₁)`.

The supporting owners were read before assembly: U024's
`RiemannSurfaceDivisorData.lean` supplies the free-abelian divisor carrier,
degree, support, nonzero chartwise meromorphic functions and principal-divisor
coefficient predicate; U025's `RiemannSurfaceDivisorEvaluationData.lean`
supplies the finite product of regular germ values with integral exponents.
The latter intentionally does not use arbitrary point values of meromorphic
representatives. These are existing source-mapped owners; the new module
adds no function field, quotient, evaluation theory, or other support stack.

This is the representative-level construction, not a claimed descended
pairing on Jacobian torsion. Existence of the chosen functions from torsion,
moving to disjoint representatives, derivation of the recorded
cross-evaluation admissibility conditions, nonvanishing, choice-independence,
the roots-of-unity target, bilinearity, and nondegeneracy remain result
clauses. No proof or new result is added.

The canonical selector was recomputed into ignored repository-local scratch.
U036 is no longer treated as a proof-free ready construction: the local owner
realizes the representative-level data and formula, while the complete source
unit remains `[sweep-iii-blocked]` and deliberately carries no `[realized]`
marker. Its first explicit construction prerequisite is U026, whose Jacobian
quotient is itself blocked at the result layer.

Source acceptance for the representative layer was completed on 2026-09-23
against the admitted Peters--Sterk Version JUNE 2024 PDF from the author URL
recorded in `provenance-contract-for-fc11-c09.md`. The downloaded 491-page
file has the recorded SHA-256
`5bc968dad21b0288f2b3d49612d94e750cd759724a16c8c25724c79410641a33`.
Direct extraction of §16.4.C matches the canonical source row. A focused
`timeout 90s lake env lean -M 1536 -o <scratch-olean>
LeanCategories/Algebra/RiemannSurfaceWeilPairingData.lean` check passed in
23.6 seconds. These validations do not discharge the blocked Jacobian-level
descent.

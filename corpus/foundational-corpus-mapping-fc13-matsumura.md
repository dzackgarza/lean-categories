---
type: reference
title: Foundational corpus mapping FC13 Matsumura
description: "# FC13 \u2014 Matsumura, *Commutative Ring Theory* mapping"
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
# Foundational corpus mapping FC13 Matsumura

# FC13 — Matsumura, *Commutative Ring Theory* mapping

Status: **Sweep II complete.** C00–C11 complete.

Canonical catalogue: [[foundational-corpus-units-fc13-matsumura|FC13 — Matsumura, Commutative Ring Theory]].

Pinned project baseline: Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0. Current Mathlib was refreshed 2026-09-07 to `e281a66114fe17935e6ea7917a01b714d0c1e493` on Lean 4.34.0-rc2; declarations first appearing after the project pin are revision-specific `reference-port` routes unless an importable package route is independently justified.

Every canonical unit receives exactly one Sweep-II route: `mathlib`, `project-existing`, `package-import`, `reference-port`, or `unmatched`. Project source is searched first, followed by pinned/current Mathlib, open/current work, Loogle/LeanSearch/Mathlib documentation, Lean Reservoir, and discoverable external Lean repositories. Strict bundle semantics apply throughout.

[Provenance contract for FC13 C00](provenance-contract-for-fc13-c00)

[Chapter 0. Conventions and terminology FC13](chapter-0-conventions-and-terminology-fc13)

[Provenance contract for FC13 C01](provenance-contract-for-fc13-c01)

[Chapter 1. Commutative rings and modules FC13](chapter-1-commutative-rings-and-modules-fc13)

[Provenance contract for FC13 C02](provenance-contract-for-fc13-c02)

[Chapter 2. Prime ideals FC13](chapter-2-prime-ideals-fc13)

[Provenance contract for FC13 C03](provenance-contract-for-fc13-c03)

[Chapter 3. Properties of extension rings FC13](chapter-3-properties-of-extension-rings-fc13)

[Provenance contract for FC13 C04](provenance-contract-for-fc13-c04)

[Chapter 4. Valuation rings, DVRs, Dedekind rings and Krull rings FC13](chapter-4-valuation-rings-dvrs-dedekind-rings-and-krull-rings-fc13)

[Provenance contract for FC13 C05](provenance-contract-for-fc13-c05)

[Chapter 5. Dimension theory FC13](chapter-5-dimension-theory-fc13)

[Provenance contract for FC13 C06](provenance-contract-for-fc13-c06)

[Chapter 6. Regular sequences, Cohen–Macaulay and Gorenstein rings FC13](chapter-6-regular-sequences-cohen-macaulay-and-gorenstein-rings-fc13)

[Provenance contract for FC13 C07](provenance-contract-for-fc13-c07)

[Chapter 7. Regular rings, UFDs and complete intersections FC13](chapter-7-regular-rings-ufds-and-complete-intersections-fc13)

[Provenance contract for FC13 C08](provenance-contract-for-fc13-c08)

[Chapter 8. Local flatness and openness loci FC13](chapter-8-local-flatness-and-openness-loci-fc13)

[Provenance contract for FC13 C09](provenance-contract-for-fc13-c09)

[Chapter 9. Differentials, separability and higher derivations FC13](chapter-9-differentials-separability-and-higher-derivations-fc13)

[Provenance contract for FC13 C10](provenance-contract-for-fc13-c10)

[Chapter 10. Adic smoothness, Cohen structure and Jacobian criteria FC13](chapter-10-adic-smoothness-cohen-structure-and-jacobian-criteria-fc13)

[Provenance contract for FC13 C11](provenance-contract-for-fc13-c11)

[Chapter 11. Catenarity, formal fibres and normalization FC13](chapter-11-catenarity-formal-fibres-and-normalization-fc13)

## Appendix A — Multilinear algebra and limits

| Unit | Match | Route | Lean owner | Provenance | Notes |
| --- | --- | --- | --- | --- | --- |
| `FC13-CA-U001` | bilinear maps are exactly curried linear maps | `mathlib` | `Mathlib/LinearAlgebra/BilinearMap.lean::LinearMap.BilinMap`, `LinearMap.mk₂` | P=db584cd6d46c92f209a44c0f1c829460d327499d | `LinearMap.BilinMap A M L` is the native type `M →ₗ[A] M →ₗ[A] L`; more generally the source's bilinear maps `M × N → L` are represented by `M →ₗ[A] N →ₗ[A] L`. `LinearMap.mk₂` constructs one from a function linear in each argument, and the linear-map instances give the stated `A`-module of bilinear maps. |
| `FC13-CA-U002` | tensor product and universal bilinear map | `mathlib` | `Mathlib/LinearAlgebra/TensorProduct/Defs.lean::TensorProduct`, `TensorProduct.mk`; `Mathlib/LinearAlgebra/TensorProduct/Basic.lean::TensorProduct.lift` | P=db584cd6d46c92f209a44c0f1c829460d327499d | `TensorProduct` is literally constructed as the quotient of `FreeAddMonoid (M × N)` by the generated zero/additivity/scalar relations. `TensorProduct.mk` is the universal bilinear map and `lift` descends every bilinear map. |
| `FC13-CA-U003` | tensor universal-property isomorphism | `mathlib` | `Mathlib/LinearAlgebra/TensorProduct/Basic.lean::TensorProduct.lift.equiv`, `TensorProduct.curry`, `TensorProduct.uncurry` | P=db584cd6d46c92f209a44c0f1c829460d327499d | `lift.equiv` is exactly the natural linear equivalence between bilinear maps `M →ₗ[A] N →ₗ[A] L` and linear maps `M ⊗[A] N →ₗ[A] L`. |
| `FC13-CA-U004` | finite multilinear tensor products and associativity | `mathlib` | `Mathlib/LinearAlgebra/PiTensorProduct/Basic.lean::PiTensorProduct.tprod`, `PiTensorProduct.lift`; `Mathlib/LinearAlgebra/TensorPower/Basic.lean::TensorPower`; `Mathlib/LinearAlgebra/TensorProduct/Associator.lean::TensorProduct.assoc` | P=db584cd6d46c92f209a44c0f1c829460d327499d | `PiTensorProduct.lift` represents arbitrary indexed multilinear maps; `TensorPower A n M` specializes to finite repeated tensor powers. `TensorProduct.assoc` is the displayed binary associativity isomorphism. |
| `FC13-CA-U005` | symmetry, unit, and direct-sum distributivity of tensor product | `mathlib` | `TensorProduct.comm`, `TensorProduct.lid`, `TensorProduct.rid`; `Mathlib/LinearAlgebra/DirectSum/TensorProduct.lean::TensorProduct.directSumLeft`, `TensorProduct.directSumRight` | P=db584cd6d46c92f209a44c0f1c829460d327499d | These are exactly Matsumura's Formulas 3–5: swap factors, tensor with the base ring, and distribute tensor product over arbitrary direct sums. |
| `FC13-CA-U006` | tensor product of linear maps | `mathlib` | `Mathlib/LinearAlgebra/TensorProduct/Map.lean::TensorProduct.map`, `TensorProduct.map_tmul` | P=db584cd6d46c92f209a44c0f1c829460d327499d | `TensorProduct.map f g` is the induced map `M ⊗ N → M' ⊗ N'` and `map_tmul` gives the source formula on pure tensors; linearity extends it to finite sums. |
| `FC13-CA-U007` | quotient formula for tensor products of two cokernels | `mathlib` | `Mathlib/LinearAlgebra/TensorProduct/Quotient.lean::TensorProduct.quotientTensorQuotientEquiv` | P=db584cd6d46c92f209a44c0f1c829460d327499d | The native equivalence identifies `(M/K) ⊗ (N/L)` with `(M ⊗ N)` modulo the supremum of the images of `K ⊗ N` and `M ⊗ L`, exactly Formula 7. |
| `FC13-CA-U008` | tensor product is right exact | `mathlib` | `Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean::TensorProduct.lTensor_exact`, `TensorProduct.rTensor_exact`, `LinearMap.lTensor_surjective`, `LinearMap.rTensor_surjective` | P=db584cd6d46c92f209a44c0f1c829460d327499d | The exactness and terminal-surjectivity declarations give the displayed right-exact tensor sequence. |
| `FC13-CA-U009` | split injections survive tensoring; flatness is exactness of tensoring | `mathlib` | `TensorProduct.map`, `LinearMap.lTensor_comp`, `LinearMap.rTensor_comp`; `Mathlib/RingTheory/Flat/Basic.lean::Module.Flat`, `Module.Flat.iff_lTensor_exact`, `Module.Flat.iff_rTensor_exact` | P=db584cd6d46c92f209a44c0f1c829460d327499d | Tensoring a split injection preserves its chosen retraction by functoriality, hence remains injective. Mathlib's `Module.Flat` and the two `iff_*Tensor_exact` theorems are exactly the source definition of flatness. |
| `FC13-CA-U010` | bimodule compatibility and induced scalar action on a tensor product | `mathlib` | `Mathlib/Algebra/Module/Bimodule.lean`; `Mathlib/LinearAlgebra/TensorProduct/Defs.lean::TensorProduct.leftModule`, `TensorProduct.tmul_smul`; `TensorProduct.comm` | P=db584cd6d46c92f209a44c0f1c829460d327499d | A commuting `A`/`B` action on `P` is native bimodule data (`SMulCommClass`/scalar towers). After swapping `M ⊗[A] P` to `P ⊗[A] M`, `TensorProduct.leftModule` induces the `B`-module action; `tmul_smul` is exactly `(m⊗p)b=m⊗(pb)` in commutative-ring notation. |
| `FC13-CA-U011` | Hom–tensor adjunction for bimodules | `mathlib` | `Mathlib/LinearAlgebra/TensorProduct/Tower.lean::TensorProduct.AlgebraTensorModule.lift.equiv`, `curry`, `uncurry`; `TensorProduct.comm`; `LinearMap.flip` | P=db584cd6d46c92f209a44c0f1c829460d327499d | The heterobasic `lift.equiv` is the required currying equivalence with two scalar rings. Swapping the tensor factors and flipping the curried linear map gives Matsumura's `Hom_A(M,Hom_B(P,N)) ≃ Hom_B(M⊗_A P,N)`. |
| `FC13-CA-U012` | associativity under change of rings | `mathlib` | `Mathlib/LinearAlgebra/TensorProduct/Tower.lean::TensorProduct.AlgebraTensorModule.assoc` | P=db584cd6d46c92f209a44c0f1c829460d327499d | `AlgebraTensorModule.assoc` is the heterobasic associator `(M ⊗[A] P) ⊗[B] N ≃ M ⊗[A] (P ⊗[B] N)` under the compatible scalar-tower hypotheses. |
| `FC13-CA-U013` | extension of scalars | `mathlib` | `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean::ModuleCat.extendScalars`, `extendRestrictScalarsAdj`; `LinearMap.baseChange` | P=db584cd6d46c92f209a44c0f1c829460d327499d | `extendScalars f` sends an `A`-module `M` to `B ⊗[A] M`; `TensorProduct.comm` identifies this with Matsumura's `M ⊗[A] B`. The file explicitly identifies this construction as extension of scalars. |
| `FC13-CA-U014` | tensor product commutes with scalar extension | `mathlib` | `TensorProduct.AlgebraTensorModule.assoc`, `cancelBaseChange`, `tensorTensorTensorComm`; `TensorProduct.comm` | P=db584cd6d46c92f209a44c0f1c829460d327499d | The displayed equivalence is the standard composite of the heterobasic associator, factor swap, and cancellation of repeated base change supplied by these native equivalences. |
| `FC13-CA-U015` | tensor product of algebras | `mathlib` | `Mathlib/RingTheory/TensorProduct/Basic.lean::Algebra.TensorProduct.instAlgebra`, `includeLeft`, `includeRight`, `tmul_mul_tmul`; `Mathlib/RingTheory/TensorProduct/Maps.lean::Algebra.TensorProduct.productMap` | P=db584cd6d46c92f209a44c0f1c829460d327499d | Mathlib equips `B ⊗[A] C` with the algebra structure satisfying `(b⊗c)(b'⊗c')=bb'⊗cc'`; `includeLeft` and `includeRight` are the two canonical generating algebra maps. |
| `FC13-CA-U016` | quotient and polynomial scalar-extension examples | `mathlib` | `Mathlib/RingTheory/TensorProduct/Quotient.lean::Algebra.TensorProduct.quotIdealMapEquivTensorQuot`; `Mathlib/RingTheory/TensorProduct/MvPolynomial.lean::MvPolynomial.algebraTensorAlgEquiv` | P=db584cd6d46c92f209a44c0f1c829460d327499d | The quotient equivalence gives `B ⊗_A (A/I) ≃ B/IB` (up to the displayed symmetric orientation). `algebraTensorAlgEquiv` gives `B ⊗_A A[X_i] ≃ B[X_i]`; one variable is the `Fin 1` specialization. |
| `FC13-CA-U017` | directed posets | `mathlib` | `Mathlib/Order/Directed.lean::IsDirected`, `IsDirectedOrder`, `SemilatticeSup.instIsDirectedOrder` | P=db584cd6d46c92f209a44c0f1c829460d327499d | `IsDirectedOrder` is exactly the common-upper-bound condition. Finite subsets ordered by inclusion form a `SemilatticeSup` under union, so the native instance supplies the standard example. |

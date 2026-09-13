---
type: reference
title: Provenance contract for FC08 C12
description: '# Provenance contract for FC08 C12'
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
# Provenance contract for FC08 C12

# Provenance contract for FC08 C12

- Canonical source block: FC08 Lee, Chapter 12, `FC08-C12-U001`–`FC08-C12-U049`, exactly 49 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order followed the Sweep-II plan: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then targeted indexed/external Lean searches. No `project-existing`, `package-import`, or `reference-port` C12 owner survived strict whole-row checking.
- C12 has 10 pinned `mathlib` rows and 39 dated `unmatched` rows. Positive rows are: U001, U004, U005, U006, U008, U009, U010, U012, U014, U027.
- The algebraic tensor-product layer is strongly covered. `MultilinearMap` owns U001; `Basis.multilinearMap` gives the dual-coordinate basis of scalar-valued multilinear maps for U004; `S →₀ ℝ` and `Finsupp.lift` give the free real vector space and its universal property for U005–U006. `PiTensorProduct` gives an indexed k-fold tensor product, pure-tensor map, relations, spanning theorem, universal property, and pure-tensor basis, owning U008–U010.
- U012 is a checked short assembly rather than an inferred equivalence. For finite-dimensional real factors, `PiTensorProduct.dualDistribEquiv` identifies the tensor product of duals with the dual of the tensor product, and `PiTensorProduct.lift` identifies that dual with scalar-valued multilinear maps. `/tmp/fc08-c12-witness.lean` compiles their canonical composite and proves the expected pure-tensor evaluation formula. The same witness typechecks U014’s k-fold-dual representation.
- U011 is deliberately not inferred from the available associators. P has `TensorProduct.assoc` and `PiTensorProduct.tmulEquiv` with exact pure-tensor formulas, but no single checked statement supplies Lee’s full pair of canonical three-factor identifications together with the stated uniqueness condition. Strict whole-row semantics keep it unmatched.
- The symmetric-tensor block U021–U026 has a clear interface boundary. `TensorPower/Symmetric.lean` defines `SymmetricPower` as a quotient by permutations, but its module documentation explicitly leaves the product and universal-property layer as TODO. Exact P/H searches found no Lee-style symmetric-multilinear subspace, averaging symmetrization projection, fixed-point theorem, or normalized symmetric product. The quotient model is not silently identified with Lee’s subspace model.
- U027 is independent of that gap: `AlternatingMap` is exactly an alternating scalar-valued multilinear map, with swap/permutation sign laws and vector-space structure. Combined with the checked U012 tensor/multilinear identification, it is an equivalent formalization of alternating covariant tensors.
- The canonical catalogue is visibly truncated at U013, U015, U017, U018, U028, and U030. These rows remain dated unmatched from the canonical text; Sweep II does not reconstruct their missing conclusions from the book.
- The manifold half U029–U049 remains blocked at a distinct abstraction boundary. P/H have no general manifold tensor-bundle/tensor-field type for covariant, contravariant, or mixed tensors. `Topology/VectorBundle/ContinuousAlternatingMap.lean` supplies a topological bundle of continuous alternating maps, while `Geometry/Manifold/VectorBundle/Tensoriality.lean` gives unary/binary tensoriality criteria on sections; neither is Lee’s arbitrary-k smooth tensor-field layer. `Analysis/Calculus/DifferentialForm/Basic.lean` separately records manifold differential forms as future work.
- Those manifold rows also inherit earlier promoted FC08 boundaries: C03 established that Lee’s tangent vectors use point derivations while Mathlib’s mature manifold vector-bundle APIs use standard `TangentSpace`, with no checked equivalence; C11 found no manifold cotangent-bundle/1-form layer. The Lie-derivative rows U042–U049 additionally depend on the C09 local/maximal-flow layer, which is absent at P/H.
- Current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` was searched by exact git object and does not add a manifold tensor-field bundle, tensor Lie derivative, symmetric-multilinear projection/product, or a bridge that closes these gaps. Targeted external searches surfaced no compatible completed Lean owner warranting `reference-port`.
- `N=2026-09-07` marks dated unmatched decisions after the prescribed search layers. Strict whole-row semantics apply uniformly.

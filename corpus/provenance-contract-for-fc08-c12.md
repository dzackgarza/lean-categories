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

- Canonical source block: FC08 Lee, Chapter 12, `FC08-C12-U001`–`FC08-C12-U049`, exactly 49 unique catalogue rows.
- The 2026-09-14 `remap-strict-bundle` pass uses clause-wise exact-route semantics. Direct tensor definitions, finite-dimensional canonical identifications, permutation averages, and recursively constructed tensor bundles are mapped through their actual algebra/vector-bundle owners rather than left unmatched for lack of Lee-specific wrapper names.
- Current route totals regenerated from the table are `mathlib` 39, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 10; total 49. Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`; current upstream was inspected at `H=87befc843c2b3a1be12f7fe9ba274d212b544348`.
- The algebraic layer U001–U028 is now essentially fully routed. `MultilinearMap.domCoprod`, `PiTensorProduct`, `TensorProduct.assoc`, `PiTensorProduct.tmulEquiv`, `dualDistribEquiv`, pure-tensor bases, and finite-dimensional duality cover Lee's products, quotient construction, associativity, abstract/concrete identifications, tensor variance conventions, bases, and dimensions. The earlier whole-row rejection of U011 was incorrect: the native associator has the exact pure-tensor formulas and uniqueness follows from spanning.
- Symmetric tensors do not require Mathlib's quotient `SymmetricPower` to match Lee's subspace model. `MultilinearMap.domDomCongr` gives the permutation action; the fixed-point submodule is Lee's symmetric subspace, finite averaging over `Equiv.Perm (Fin k)` gives symmetrization, and `domCoprod` followed by the average gives the symmetric product. The standard finite-group averaging arguments establish U024–U026. `AlternatingMap` remains the exact alternating counterpart.
- The manifold tensor-bundle premise in the 2026-09-07 contract is also obsolete. Mathlib's smooth bundle of continuous linear maps (`Topology/VectorBundle/Hom.lean` and `Geometry/Manifold/VectorBundle/Hom.lean`) can be iterated: starting from the tangent bundle and scalar line gives curried covariant tensors; starting from the cotangent bundle gives contravariant tensors; mixing primal and dual argument bundles gives arbitrary mixed tensors. `ContMDiffSection` then supplies smooth tensor fields. Finite-dimensional continuity makes this equivalent to Lee's algebraic multilinear fibers.
- U032 component functions are the local trivialization coordinates of those recursive hom-bundles. U034 tensor products and U038–U040 pullbacks assemble from `domCoprod`, smooth hom-bundle composition/application, and the smooth tangent map/chain rule. These are finite native assemblies, not missing abstractions.
- The general smoothness/characterization boundary remains real. `VectorBundle/Tensoriality.lean` provides locality, pointwise dependence, and reconstruction for unary and binary tensorial operations (`TensorialAt.mkHom`, `mkHom₂`), but no arbitrary-arity theorem matching Lee's complete U033/U035 equivalences. Live corpus searches for an arbitrary `C∞(M)`-multilinear tensor characterization found no exact owner, so U033 and U035 remain `unmatched`.
- U041 remains an explicit polar-coordinate calculation rather than an absent abstraction. All ingredients are routed by U040 and real calculus, but no checked source owns Lee's displayed multi-term identity.
- U042 is only the definition of tensor Lie derivative as the derivative at zero of the flow pullback and is directly expressible from flow, tensor pullback, and ordinary derivative primitives. Exact searches of current Mathlib, TauCeti, OpenGA, Atlas, and the live formalization corpus found no proof-complete arbitrary covariant-tensor `LieDerivative` theorem package. Thus U043–U049 remain theorem-level residuals; keyword hits were covariant-derivative/Koszul material or Euclidean differential-form code, not Lee's tensor Lie derivative.
- TauCeti current HEAD `35469bdd4baafcaf1da88fba1e6f6d66d623aaac` does contain a proof-complete `SmoothTwoForm` rank-two specialization and extensive covariant-derivative tensoriality, confirming the recursive-hom-bundle model, but it does not close the arbitrary-rank Lie-derivative tail. Search errors are never used as negative evidence.

---
title: "FC08 — John M. Lee, Introduction to Smooth Manifolds, 2nd ed. (2013)"
---

FC08 — Lee, *Introduction to Smooth Manifolds* — block `FC08-CC`.

50 units. 23 have a Lean owner; 27 do not.

| Route | Units | Share | Meaning |
| --- | ---: | ---: | --- |
| [`unmatched`]{.route-unmatched} | 27 | 54% | No checked Lean owner was found. |
| [`mathlib`]{.route-mathlib} | 23 | 46% | Mathlib owns the unit outright. |
| **total** | **50** | | |

::: {.callout-note collapse="true"}
## How this chapter was searched

- Canonical source block: FC08 Lee, Appendix C, `FC08-CC-U001`–`FC08-CC-U050`, exactly 50 unique contiguous rows retrieved from [FC08 — John M. Lee, Introduction to Smooth Manifolds](/sources/fc08/) through `agent-memory`.
- Search order: project at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then current/open/indexed services, Reservoir/package candidates, broad GitHub Lean repositories, and local reference sources. No `project-existing`, `package-import`, or `reference-port` route survived strict whole-row checking.
- Appendix C has 23 pinned `mathlib` rows and 27 dated `unmatched` rows. Positive rows are: U001, U002, U003, U004, U005, U006, U007, U008, U011, U012, U014, U015, U016, U017, U027, U035, U041, U043, U044, U045, U046, U048, U050.
- `/tmp/fc08-cc-witness.lean` compiles at exact P and checks the principal calculus routes: Fréchet derivatives and chain rule, line derivatives, second-derivative symmetry, Taylor/parametric-integral adjacency, Fubini/Bochner integration adjacency, local Lipschitz results, uniform-series M-test, inverse function theorem, Banach contraction, and implicit function theorem.
- Mathlib’s Fréchet calculus provides exact coordinate-free owners for Lee’s total derivative, chain rule, `C^k` regularity, and local inverse/implicit-function results. `lineDeriv` supplies the exact one-variable derivative along a standard basis vector, so source partial derivatives and Jacobian entries are short canonical assemblies rather than new definitions.
- The main negative boundary is representational and deliberate. Lee builds multidimensional integration through Darboux sums and a Riemann integral on bounded domains; pinned/current Mathlib uses Lebesgue/Bochner integration. Mathlib has stronger Fubini, vector-integral, norm-integral, set-volume, and Jacobian change-of-variables results, but no checked Riemann–Lebesgue equivalence for Lee’s interface. Therefore U021–U026 and U028–U039 remain unmatched except for the representation-independent null-set theorem U027 and Corollary U035.
- `map_add_eq_sum_add_integral_iteratedFDeriv` gives a strong coordinate-free Taylor theorem, but Lee’s U019 is the explicit all-orders multi-index partial-derivative formula. Because the all-orders mixed-partial permutation bridge in U013 was not found, U019/U020 are not promoted by silently translating representations.
- The polar-coordinate example U048 has an unusually exact pinned owner: `polarCoord` is the open partial homeomorphism between the slit plane and `(0,∞)×(-π,π)`, its inverse is Lee’s `(r cos θ,r sin θ)`, and `det_fderivPolarCoordSymm` computes determinant `r`. No corresponding full spherical-coordinate owner was found for U049.
- Broad GitHub searches on 2026-09-07 did not surface a compatible Lean 4 implementation of Lee’s multidimensional Darboux/Riemann layer or a missing Jacobian/partial-derivative bundle. Current repositories found in the ODE/control direction either reuse Mathlib or explicitly axiomatize ODE existence results, so they do not improve Appendix C routes.
- `N=2026-09-07` marks dated unmatched decisions. Strict whole-row semantics apply uniformly.
:::

### **Definition/convention — differentiable at a** {#fc08-cc-u001}

::: {.unit-meta}
`FC08-CC-U001` · Appendix C, § Total and Partial Derivatives; source L19458 · [`mathlib`]{.route-mathlib}
:::

Let V , W be finite-dimensional vector spaces, which we may assume to be endowed with norms. If U ⊆ V is an open subset and a ∈ U , a map F : U → W is said to be differentiable at a if there exists a linear map L : V → W such that lim _v → 0 (∣ F (a + v) - F (a) - L v ∣)/(∣ v ∣) = 0.tagC.1

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/FDeriv/Defs.lean::HasFDerivWithinAt, HasFDerivAt, fderivWithin, fderiv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/FDeriv/Defs.html) — Mathlib’s Fréchet derivative is exactly Lee’s total derivative: `HasFDerivWithinAt` gives the little-o linear approximation on a set, and on an open domain it agrees with `HasFDerivAt`; `fderivWithin`/`fderiv` are the unique derivative maps.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Definition/convention — total derivative of F at a** {#fc08-cc-u002}

::: {.unit-meta}
`FC08-CC-U002` · Appendix C, § Total and Partial Derivatives; source L19468 · [`mathlib`]{.route-mathlib}
:::

If F is differentiable at a, the linear map L satisfying (C.1) is denoted by D F ( a ) and is called the total derivative of F at a. Condition (C.1) can also be written

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/FDeriv/Defs.lean::HasFDerivWithinAt, HasFDerivAt, fderivWithin, fderiv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/FDeriv/Defs.html) — Mathlib’s Fréchet derivative is exactly Lee’s total derivative: `HasFDerivWithinAt` gives the little-o linear approximation on a set, and on an open domain it agrees with `HasFDerivAt`; `fderivWithin`/`fderiv` are the unique derivative maps.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Proposition C.3** {#fc08-cc-u003}

::: {.unit-meta}
`FC08-CC-U003` · Appendix C, § Total and Partial Derivatives; source L19508 · [`mathlib`]{.route-mathlib}
:::

(The Chain Rule for Total Derivatives). Suppose V , W , X are finite-dimensional vector spaces, U ⊆ V and tilde(U) ⊆ W are open subsets, and F : U → tilde(U) and G : tilde(U) → X are maps. If F is differentiable at a ∈ U and G is differentiable at F ( a ) ∈ tilde(U) , then G ∘ F is differentiable at a, and D (G ∘ F) (a) = D G (F (a)) ∘ D F (a).

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/FDeriv/Comp.lean::HasFDerivAt.comp, HasFDerivWithinAt.comp`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/FDeriv/Comp.html) — The Fréchet chain rule composes the derivative linear maps exactly as in Proposition C.3, and applies on open Euclidean domains via the within/at bridge.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Definition/convention — source terminology/construction** {#fc08-cc-u004}

::: {.unit-meta}
`FC08-CC-U004` · Appendix C, § Partial Derivatives; source L19548 · [`mathlib`]{.route-mathlib}
:::

Now we specialize to maps between Euclidean spaces. Suppose U ⊆ ℝ ^n is open and f : U → ℝ is a real-valued function. For any a = ( a ^1 , … , a ^n ) ∈ U and any j ∈ 1 , …c , n , the j th partial derivative of f at a is defined to be the ordinary derivative of f with respect to x ^j while holding the other variables fixed: beginarrayc (∂ f)/(∂ x ^j) (a) = lim _h → 0 (f (a ^1 , … , a ^j + h , … , a ^n) - f (a ^1 , … , a ^j , … , a ^n))/(h) = lim _h → 0 (f (a + h e _j) - f (a))/(h), endarray

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/LineDeriv/Basic.lean::lineDerivWithin, lineDeriv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/LineDeriv/Basic.html) — Lee’s partial derivative is exactly the line derivative in the standard-basis direction `e_j`; `lineDerivWithin ℝ f U a e_j` is defined by the same one-variable difference quotient.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Definition/convention — component functions of F** {#fc08-cc-u005}

::: {.unit-meta}
`FC08-CC-U005` · Appendix C, § Partial Derivatives; source L19556 · [`mathlib`]{.route-mathlib}
:::

More generally, for a vector-valued function F : U ℝ ^m , we can write the coordinates of F ( x ) as F ( x ) = ( F ^1 ( x ) , … , F ^m ( x ) ) This defines m functions F ^1 , … , F ^m : U R called the component functions of F . The partial derivatives of F are defined simply to be the partial derivatives ∂ F ^i / ∂ x ^j of its component functions. The matrix ( ∂ F ^i / ∂ x ^j ) of partial derivatives is called the Jacobian matrix of F , and its determinant is called the Jacobian determinant of F

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/LineDeriv/Basic.lean::lineDerivWithin`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/LineDeriv/Basic.html); [`Mathlib/Data/Matrix/Basic.lean::Matrix`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Basic.html); [`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean::Matrix.det`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html#Matrix.det) — For `F : ℝ^n → ℝ^m`, component functions are coordinate evaluations; the Jacobian is the matrix `(i,j) ↦ lineDerivWithin ℝ (fun x => F x i) U a e_j`, and [`Matrix.det`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.det#doc) is its determinant in the square case. This is an exact short assembly of canonical Mathlib objects even though Mathlib has no separately named `Jacobian` definition.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Definition/convention — of class C** {#fc08-cc-u006}

::: {.unit-meta}
`FC08-CC-U006` · Appendix C, § Partial Derivatives; source L19558 · [`mathlib`]{.route-mathlib}
:::

If F : U ℝ ^m is a function for which each partial derivative exists at each point in U and the functions ∂ F ^i / ∂ x ^j : U → ℝ so defined are all continuous, then F is said to be of class C ^1 or continuously differentiable. If this is the case, we can differentiate the functions ∂ F ^i / ∂ x ^j to obtain second-order partial derivatives

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/ContDiff/Defs.lean::ContDiffOn, ContDiff`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/ContDiff/Defs.html) — `ContDiffOn ℝ k F U` is Mathlib’s `C^k` predicate and `ContDiffOn ℝ ∞ F U` is smoothness; the definition is local and agrees with the usual Euclidean partial-derivative formulation.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Definition/convention — of class C** {#fc08-cc-u007}

::: {.unit-meta}
`FC08-CC-U007` · Appendix C, § Partial Derivatives; source L19566 · [`mathlib`]{.route-mathlib}
:::

In general, if U ⊆ ℝ ^n is an open subset and k ≥ 0 , a function F : U ℝ ^m is said to be of class C ^k or k times continuously differentiable if all the partial derivatives of F of order less than or equal to k exist and are continuous functions on U . (Thus a function of class C ^0 is just a continuous function.) Because existence and continuity of derivatives are local properties, clearly F is C ^k if and only if it has that property in a neighborhood of each point in U

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/ContDiff/Defs.lean::ContDiffOn, ContDiff`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/ContDiff/Defs.html) — `ContDiffOn ℝ k F U` is Mathlib’s `C^k` predicate and `ContDiffOn ℝ ∞ F U` is smoothness; the definition is local and agrees with the usual Euclidean partial-derivative formulation.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Definition/convention — diffeomorphism** {#fc08-cc-u008}

::: {.unit-meta}
`FC08-CC-U008` · Appendix C, § Partial Derivatives; source L19568 · [`mathlib`]{.route-mathlib}
:::

A function that is of class C ^k for every k ≥ 0 is said to be of class C ^∞ , smooth, or infinitely differentiable. If U and V are open subsets of Euclidean spaces, a function F : U → V is called a diffeomorphism if it is smooth and bijective and its inverse function is also smooth.

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/ContDiff/Defs.lean::ContDiffOn`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/ContDiff/Defs.html); `Lean core::Function.Bijective, Function.invFun` — Lee’s Euclidean diffeomorphism definition is the exact conjunction that `F` is smooth on `U`, bijective onto `V`, and its inverse is smooth on `V`; these are canonical Lean/Mathlib predicates, requiring no new mathematical owner.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Proposition C.4** {#fc08-cc-u009}

::: {.unit-meta}
`FC08-CC-U009` · Appendix C, § Partial Derivatives; source L19572 · [`unmatched`]{.route-unmatched}
:::

Suppose U ⊆ ℝ ^n and V ⊆ ℝ ^m are open subsets and F : U → V is a diffeomorphism. Then m = n , and for each a ∈ U , the total derivative D F ( a ) is invertible, with D F ( a ) ^- 1 = D ( F ^- 1 ) ( F ( a ) )

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Pinned/current Mathlib has the Fréchet chain rule and local inverse theorems, but no checked theorem was found that starts from Lee’s source-level “smooth bijection with smooth inverse between open Euclidean subsets” bundle and simultaneously gives equality of ambient dimensions plus the exact inverse-total-derivative formula. Reconstructing the subtype/open-domain bookkeeping would be substantive. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Definition/convention — smooth** {#fc08-cc-u010}

::: {.unit-meta}
`FC08-CC-U010` · Appendix C, § Partial Derivatives; source L19582 · [`unmatched`]{.route-unmatched}
:::

We sometimes need to consider smoothness of functions whose domains are subsets of ℝ ^n that are not open. If A ⊆ ℝ ^n is an arbitrary subset, a function F : A → ℝ ^m is said to be smooth on A if it admits a smooth extension to an open neighborhood of each point, or more precisely, if for every x ∈ A , there exist an open subset U _x ⊆ ℝ ^n containing x and a smooth function tilde(F) : U _x → ℝ ^m that agrees with F on U _x ∩ A . The notion of diffeomorphism extends to arbitrary subsets in the obvious way: given arbitrary subsets A , B ⊆ ℝ ^n , a diffeomorphism from A to B is a smooth bijective map f : A → B with smooth inverse.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Mathlib’s `ContDiffWithinAt` is an intrinsic within-set smoothness notion; the source defines smoothness on an arbitrary subset by existence of local smooth ambient extensions. No checked equivalence between these notions for arbitrary subsets was found. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Definition/convention — source terminology/construction** {#fc08-cc-u011}

::: {.unit-meta}
`FC08-CC-U011` · Appendix C, § Partial Derivatives; source L19584 · [`mathlib`]{.route-mathlib}
:::

We are especially concerned with real-valued functions, that is, functions whose codomain is R. If U ⊆ ℝ ^n is open, the set of all real-valued functions of class C ^k on U is denoted by C ^k ( U ) , and the set of all smooth real-valued functions by C ^∞ ( U ) . Sums, constant multiples, and products of functions are defined pointwise: for f , g : U → ℝ and c ∈ ℝ

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/ContDiff/Defs.lean::ContDiffOn`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/ContDiff/Defs.html); [`Mathlib/Analysis/Calculus/ContDiff/Operations.lean::ContDiffOn.add, ContDiffOn.const_smul, ContDiffOn.mul`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/ContDiff/Operations.html) — `C^k(U)` is the set of real-valued maps satisfying `ContDiffOn`; Mathlib proves closure under pointwise addition, scalar multiplication, and multiplication exactly as stated.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Proposition C.6** {#fc08-cc-u012}

::: {.unit-meta}
`FC08-CC-U012` · Appendix C, § Partial Derivatives; source L19600 · [`mathlib`]{.route-mathlib}
:::

(Equality of Mixed Partial Derivatives). If U is an open subset of ℝ ^n and F U → ℝ ^m is a function of class C ^2 , then the mixed second-order partial derivatives of F do not depend on the order of differentiation: (∂^2 F ^i)/(∂ x ^j ∂ x ^k) = (∂^2 F ^i)/(∂ x ^k ∂ x ^j).

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean::second_derivative_symmetric, ContDiffAt.isSymmSndFDerivAt`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/FDeriv/Symmetric.html#ContDiffAt.isSymmSndFDerivAt) — Mathlib proves symmetry of the second Fréchet derivative for `C²` maps. Evaluating the symmetric bilinear derivative on standard basis vectors gives equality of Lee’s mixed second partial derivatives componentwise.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Corollary C.7** {#fc08-cc-u013}

::: {.unit-meta}
`FC08-CC-U013` · Appendix C, § Partial Derivatives; source L19606 · [`unmatched`]{.route-unmatched}
:::

If F : U ℝ ^m is smooth, then the mixed partial derivatives of F of any order are independent of the order of differentiation.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Mathlib directly proves symmetry of second Fréchet derivatives, but targeted P/H searches found no checked all-orders permutation-invariance theorem for coordinate mixed partials matching this row. Iterated Fréchet derivatives/Taylor-series infrastructure is adjacent but does not by itself certify the exact statement. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Proposition C.8** {#fc08-cc-u014}

::: {.unit-meta}
`FC08-CC-U014` · Appendix C, § Partial Derivatives; source L19610 · [`mathlib`]{.route-mathlib}
:::

Let U ⊆ ℝ ^n be open, and suppose F : U ℝ ^m is differentiable at a ∈ U . Then all of the partial derivatives of F at a exist, and D F ( a ) is the linear map whose matrix is the Jacobian of F at a: D F (a) = ((∂ F ^j)/(∂ x ^i) (a) ).

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/LineDeriv/Basic.lean::DifferentiableAt.lineDeriv_eq_fderiv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/LineDeriv/Basic.html#DifferentiableAt.lineDeriv_eq_fderiv); [`Mathlib/LinearAlgebra/Matrix/ToLin.lean::LinearMap.toMatrix`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/ToLin.html#LinearMap.toMatrix) — For a differentiable map, every line derivative equals evaluation of `fderiv`; in standard bases, [`LinearMap.toMatrix`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.toMatrix#doc) therefore has entries equal to the coordinate partial derivatives, exactly Proposition C.8.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Proposition C.10** {#fc08-cc-u015}

::: {.unit-meta}
`FC08-CC-U015` · Appendix C, § Partial Derivatives; source L19634 · [`mathlib`]{.route-mathlib}
:::

Let U ⊆ ℝ ^n be open. If F : U ℝ ^m is of class C ^1 , then it is differentiable at each point of U .

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/ContDiff/Defs.lean::ContDiffOn.differentiableOn, ContDiffOn.differentiableOn_one`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/ContDiff/Defs.html) — Mathlib directly proves that a `C¹` map is differentiable at every point of its domain.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Corollary C.11** {#fc08-cc-u016}

::: {.unit-meta}
`FC08-CC-U016` · Appendix C, § Partial Derivatives; source L19638 · [`mathlib`]{.route-mathlib}
:::

(The Chain Rule for Partial Derivatives). Let U ⊆ ℝ ^n and widetilde U ⊆ R m be open subsets, and let x = ( x ^1 , … , x ^n ) denote the standard coordinates on U and y = ( y ^1 , … , y ^m ) those on tilde(U) (a) A composition of C ^1 functions F : U → tilde(U) and G : tilde(U) → ℝ ^p is again of class C ^1 , with partial derivatives given by (∂ (G ^i ∘ F))/(∂ x ^j) (x) = sum_k = 1 ^m (∂ G ^i)/(∂ y ^k) (F (x) ) (∂ F ^k)/(∂ x ^j) (x). (b) If F and G are smooth, then G F is smooth.

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/ContDiff/Comp.lean::ContDiffOn.comp`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/ContDiff/Comp.html#ContDiffOn.comp); [`Mathlib/Analysis/Calculus/FDeriv/Comp.lean::fderiv_comp`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/FDeriv/Comp.html); [`Mathlib/Analysis/Calculus/LineDeriv/Basic.lean::DifferentiableAt.lineDeriv_eq_fderiv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/LineDeriv/Basic.html#DifferentiableAt.lineDeriv_eq_fderiv) — [`ContDiffOn.comp`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ContDiffOn.comp#doc) gives preservation of `C¹`/smoothness under composition; `fderiv_comp` and `lineDeriv_eq_fderiv` translate the Fréchet chain rule to the standard-coordinate partial-derivative sum in C.11(a).
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Definition/convention — directional derivative of f in the direction v at a to be the** {#fc08-cc-u017}

::: {.unit-meta}
`FC08-CC-U017` · Appendix C, § Partial Derivatives; source L19654 · [`mathlib`]{.route-mathlib}
:::

Now suppose f : U → ℝ is a smooth real-valued function on an open subset U ⊆ ℝ ^n , and a ∈ U . For each vector v ∈ ℝ ^n , we define the directional derivative of f in the direction v at a to be the number

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/LineDeriv/Basic.lean::lineDeriv, HasLineDerivAt`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/LineDeriv/Basic.html) — `lineDeriv ℝ f a v` is exactly Lee’s directional derivative along the line `a + t v`; for smooth `f` it equals `fderiv ℝ f a v`.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Theorem C.14** {#fc08-cc-u018}

::: {.unit-meta}
`FC08-CC-U018` · Appendix C, § Partial Derivatives; source L19670 · [`unmatched`]{.route-unmatched}
:::

(Differentiation Under an Integral Sign). Let U ⊆ ℝ ^n be an open subset, let a , b ∈ ℝ , and let f : U × [ a , b ] → ℝ be a continuous function such that the partial derivatives ∂ f / ∂ x ^i : U × [ a , b ] → ℝ exist and are continuous on U × Œa; b for i = 1 , … , n . Define F : U → R by F (x) = int_a ^b f (x, t) d t. Then F is of class C ^1 , and its partial derivatives can be computed by differentiating under the integral sign: (∂ F)/(∂ x ^i) (x) = int_a ^b (∂ f)/(∂ x ^i) (x, t) d t. You are probably familiar with Taylor’s theorem, which shows how a sufficiently smooth function can be approximated near a point by a polynomial. We need a version of Taylor’s theorem in several variables that gives an explicit integral form for the remainder term. In order to express it concisely, it helps to introduce some shorthand notation. For any m-tuple I = ( i _1 , … , i _m ) of indices with 1 ≤ i _j ≤ n , we let ∣ I ∣ = m denote the number of indices in I , and beginarrayc partial_I = frac ∂^m∂ x ^ i _1 ·s ∂ x ^ i _m, (x - a) ^I = (x ^ i _1 - a ^ i _1 ) … (x ^ i _m - a ^ i _m ). endarray

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Mathlib has a strong parametric differentiation-under-the-integral theorem, but this canonical row also introduces the multi-index notation used for Taylor’s theorem. No single checked route owns the whole bundle. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Theorem C.15** {#fc08-cc-u019}

::: {.unit-meta}
`FC08-CC-U019` · Appendix C, § Partial Derivatives; source L19688 · [`unmatched`]{.route-unmatched}
:::

(Taylor’s Theorem). Let U ⊆ ℝ ^n be an open subset, and let a ∈ U be fixed. Suppose f ∈ C ^k + 1 ( U ) for some k ≥ 0 . If W is any convex subset of U containing a, then for all x ∈ W f (x) = P _k (x) + R _k (x),tagC.7 where P _k is the kth-order Taylor polynomial of f at a, defined by P _k (x) = f (a) + sum_m = 1 ^k (1)/(m !) sum_I: ∣ I ∣ = m partial_I f (a) (x - a) ^I,tagC.8 and R _k is the kth remainder term, given by R _k (x) = (1)/(k !) sum_I: ∣ I ∣ = k + 1 (x - a) ^I int_0 ^1 (1 - t) ^k partial_I f (a + t (x - a)) d t.tagC.9

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — `map_add_eq_sum_add_integral_iteratedFDeriv` is a stronger coordinate-free Taylor formula with integral remainder, but the source row is the explicit multi-index partial-derivative expansion. Because U013’s all-orders mixed-partial bridge is not checked, the two interfaces are not silently identified. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Corollary C.16** {#fc08-cc-u020}

::: {.unit-meta}
`FC08-CC-U020` · Appendix C, § Partial Derivatives; source L19718 · [`unmatched`]{.route-unmatched}
:::

Suppose U ⊆ ℝ ^n is an open subset, a ∈ U , and f ∈ C ^k + 1 ( U ) f o r some k ≥ 0 . H W is a convex subset of U containing a on which all of the ( k + 1 ) s t partial derivatives of f are bounded in absolute value by a constant M; then for all x ∈ W ∣ f (x) - P _k (x) ∣ ≤ (n ^k + 1 M)/((k + 1) !) ∣ x - a ∣ ^k + 1, where P _k is the kth Taylor polynomial of f at a, defined by (C.8).

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Mathlib’s Taylor-integral and derivative-bound APIs are adjacent, but no checked theorem with Lee’s explicit `n^(k+1) M/(k+1)!` remainder constant and source partial-derivative hypotheses was found. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Definition/convention — open rectangle** {#fc08-cc-u021}

::: {.unit-meta}
`FC08-CC-U021` · Appendix C, § Multiple Integrals; source L19732 · [`unmatched`]{.route-unmatched}
:::

A closed rectangle in ℝ ^n is a product set of the form [ a ^1 , b ^1 ] × ·s × [ a ^n , b ^n ] , for real numbers a ^i < b ^i . Analogously, an open rectangle is a set of the form ( a ^1 , b ^1 ) × ·s × ( a ^n , b ^n ) . If A is a rectangle of either type, the volume of A, denoted by Vol.A/, is defined to be the product of the lengths of its component intervals: Vol (A) = (b ^1 - a ^1 ) … (b ^n - a ^n ).tagC.10

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Mathlib represents coordinate boxes using products/Pi `Icc` and `Ioo` sets and Lebesgue volume, but no canonical owner packages Lee’s closed/open rectangle terminology together with the source side-length volume definition. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Definition/convention — cube** {#fc08-cc-u022}

::: {.unit-meta}
`FC08-CC-U022` · Appendix C, § Multiple Integrals; source L19738 · [`unmatched`]{.route-unmatched}
:::

A rectangle is called a cube if all of its side lengths ( b ^i - a ^i ) are equal.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No canonical Lean object was found for the source-specific term “cube” as a rectangle whose side lengths are all equal; the underlying interval/product ingredients are proper subsets. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Definition/convention — subinterval of P** {#fc08-cc-u023}

::: {.unit-meta}
`FC08-CC-U023` · Appendix C, § Multiple Integrals; source L19740 · [`unmatched`]{.route-unmatched}
:::

Given a closed interval [ a , b ] ⊆ ℝ , a partition of Œa; b is a finite sequence P = ( a _0 , … , a _k ) of real numbers such that a = a _0 < a _1 < ·s < a _k = b . Each of the intervals [ a _i - 1 , a _i ] for i = 1 , … , k is called a subinterval of P . Similarly, if A = [ a ^1 , b ^1 ] dot × dot ·s × [ dot a ^n , b ^n ] is a closed rectangle, a partition of A is an n-tuple P = ( P _1 , … , P _n ) , where each P _i is a partition of [ a ^i , b ^i ] . Each rectangle of the form I _1 × ·s × I _n , where I _j is a subinterval of P _j , is called a subrectangle of P . Clearly, A is the union of all the subrectangles in any partition, and distinct subrectangles intersect only on their boundaries.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Mathlib has finite ordered sets, intervals, and finite box decompositions, but no checked canonical construction matching Lee’s Riemann partition/subrectangle bundle. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Definition/convention — lower sum of f** {#fc08-cc-u024}

::: {.unit-meta}
`FC08-CC-U024` · Appendix C, § Multiple Integrals; source L19742 · [`unmatched`]{.route-unmatched}
:::

Suppose A ⊆ ℝ ^n is a closed rectangle and f : A → ℝ is a bounded function. For each partition P of A, we define the lower sum of f with respect to P by L (f, P) = sum_j (inf _ R _j f ) Vol (R _j),

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Pinned/current Mathlib does not formalize Lee’s multidimensional Darboux lower/upper sums as the canonical integration interface. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Lemma C.17** {#fc08-cc-u025}

::: {.unit-meta}
`FC08-CC-U025` · Appendix C, § Multiple Integrals; source L19756 · [`unmatched`]{.route-unmatched}
:::

Let A ⊆ ℝ ^n be a closed rectangle, and let f : A → ℝ be a bounded function. For any pair of partitions P and P 0 of A, L (f, P) ≤ U (f, P ^prime).

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked multidimensional Darboux-sum theorem matching the source statement was found because the source lower/upper-sum layer itself is absent. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Convention/notation — integral of f** {#fc08-cc-u026}

::: {.unit-meta}
`FC08-CC-U026` · Appendix C, § Multiple Integrals; source L19786 · [`unmatched`]{.route-unmatched}
:::

If f : A → ℝ is a bounded function whose upper and lower integrals are equal, we say that f is (Riemann) integrable over A, and their common value, denoted by int_A f d V, is called the integral of f over A. The " d V " in this notation, like the ^6 6 d x ^, 5 9 in the notation for single integrals, has no meaning on its own; it is just a “closing bracket” for the integral sign. Other common notations are int_A f text or int_A f d x ^1 … d x ^n text or int_A f (x ^1, … , x ^n) d x ^1 … d x ^n. In ℝ ^2 , the symbol d V is often replaced by dA.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Pinned/current Mathlib’s standard integral is Lebesgue/Bochner rather than Lee’s multidimensional Riemann integral defined by equality of Darboux upper/lower integrals. No checked equivalence layer was found. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Proposition C.18** {#fc08-cc-u027}

::: {.unit-meta}
`FC08-CC-U027` · Appendix C, § Multiple Integrals; source L19802 · [`mathlib`]{.route-mathlib}
:::

(Properties of Sets of Measure Zero). (a) I f X ⊆ ℝ ^n has measure zero and x _0 ∈ ℝ ^n , then the translated subset x _0 + X = x _0 + a : a ∈ X also has measure zero. (b) Every subset of a set of measure zero in ℝ ^n has measure zero. (c) A countable union of sets of measure zero in ℝ ^n has measure zero. (d) I f k < n , then every subset of ℝ ^k (viewed as the set of points x ∈ ℝ ^n with x ^k + 1 = ·s = x ^n = 0 ) has measure zero in ℝ ^n

::: {.unit-lean}
**In Lean.** [`Mathlib/MeasureTheory/Group/Measure.lean::Measure.IsAddLeftInvariant`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Group/Measure.html#Measure.IsAddLeftInvariant); [`Mathlib/MeasureTheory/OuterMeasure/Basic.lean::measure_mono_null, measure_iUnion_null`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/OuterMeasure/Basic.html); [`Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean::addHaar_submodule`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.html) — Lebesgue volume is translation invariant; nullity is inherited by subsets and countable unions; and every strict finite-dimensional real linear subspace has Haar/Lebesgue measure zero. The coordinate copy of `ℝ^k` for `k<n` is such a strict subspace, giving all four clauses.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Proposition C.20** {#fc08-cc-u028}

::: {.unit-meta}
`FC08-CC-U028` · Appendix C, § Multiple Integrals; source L19818 · [`unmatched`]{.route-unmatched}
:::

(Lebesgue’s Integrability Criterion). Let A ⊆ ℝ ^n be a closed rectangle, and let f : A → ℝ be a bounded function. If the set S = x ∈ A: f text is not continuous at x has measure zero, then f is integrable.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Mathlib has Lebesgue/Bochner integrability, but no checked formalization of Lebesgue’s criterion for Lee’s multidimensional Riemann integrability. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Definition/convention — integral of f** {#fc08-cc-u029}

::: {.unit-meta}
`FC08-CC-U029` · Appendix C, § Multiple Integrals; source L19846 · [`unmatched`]{.route-unmatched}
:::

Now suppose D ⊆ ℝ ^n is an arbitrary bounded set, and f : D → ℝ is a bounded function. Define f _D : ℝ ^n → ℝ by f _D (x) = beginarrayl l f (x), & x ∈ D, 0, & x ∈ ℝ ^n smallsetminus D. endarray .tagC.11 If the integral int_A f _D d VtagC.12 exists for some closed rectangle A containing D, then f is said to be integrable over D. The integral (C.12) is denoted by scriptstyle int _D f dV and called the integral of f over D. It is easy to check that both the integrability of f and the value of the integral are independent of the rectangle chosen.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked owner was found for Lee’s extension-by-zero definition of the multidimensional Riemann integral over an arbitrary bounded set. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Definition/convention — domain of integration** {#fc08-cc-u030}

::: {.unit-meta}
`FC08-CC-U030` · Appendix C, § Multiple Integrals; source L19862 · after [`FC08-CC-U027`](#fc08-cc-u027) · [`unmatched`]{.route-unmatched}
:::

A subset D ⊆ ℝ ^n is called a domain of integration if D is bounded and @D has n-dimensional measure zero. It follows from Proposition C.18 that every open or closed rectangle is a domain of integration, and a finite union of domains of integration is again a domain of integration.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Mathlib has bounded sets, topological boundary, and null sets, but no canonical `domain of integration` object bundling exactly “bounded with boundary of Lebesgue measure zero.” Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Proposition C.21** {#fc08-cc-u031}

::: {.unit-meta}
`FC08-CC-U031` · Appendix C, § Multiple Integrals; source L19864 · [`unmatched`]{.route-unmatched}
:::

If D ⊆ ℝ ^n is a domain of integration, then every bounded continuous real-valued function on D is integrable over D

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Mathlib proves bounded continuous functions on finite-measure sets are Bochner/Lebesgue integrable under standard hypotheses, but no checked bridge to Lee’s absent multidimensional Riemann integral exists. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Definition/convention — source terminology/construction** {#fc08-cc-u032}

::: {.unit-meta}
`FC08-CC-U032` · Appendix C, § Multiple Integrals; source L19872 · [`unmatched`]{.route-unmatched}
:::

If D is a domain of integration, the volume of D is defined to be Vol (D) = int_D 1 d V.tagC.13

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — `setIntegral_one_eq_measureReal` gives volume as the Lebesgue integral of `1`, but Lee’s row defines volume via the preceding Riemann integral. Without a checked Riemann–Lebesgue equivalence this is only an adjacent representation. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Proposition C.22** {#fc08-cc-u033}

::: {.unit-meta}
`FC08-CC-U033` · Appendix C, § Multiple Integrals; source L19882 · [`unmatched`]{.route-unmatched}
:::

(Properties of Volume). Let D ⊆ ℝ ^n be a domain of integration. (a) If D is an open or closed rectangle, then the two definitions (C.10) and (C.13) of Vol.D/ agree. (b) V o l ( D ) ≥ 0 , with equality if and only if D has measure zero. (c) f f D _1 , … , D _k are domains of integration whose union is D, then Vol (D) ≤ Vol (D _1) + … + Vol (D _k), with equality if and only if D _i ∩ D _j has measure zero for each i ≠ j (d) If D _1 is a domain of integration contained in D _: , then V o l ( D _1 ) ≤ V o l ( D ) , with equality i f and only if D setminus D _1 has measure zero.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Mathlib’s measure API has the corresponding monotonicity/subadditivity/null-set facts, but the row asserts them for Lee’s Riemann-defined volume and includes exact equality iff conditions. No checked whole-row bridge to that source interface exists. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Proposition C.23** {#fc08-cc-u034}

::: {.unit-meta}
`FC08-CC-U034` · Appendix C, § Multiple Integrals; source L19896 · [`unmatched`]{.route-unmatched}
:::

(Properties of Integrals). Let D ⊆ ℝ ^n be a domain of integration, and let f , g : D → ℝ be continuous and bounded. (a) For any a , b ∈ ℝ int_D (a f + b g) d V = a int_D f d V + b int_D g d V. (b) If D has measure zero, then textstyle int _D f d V = 0 (c) f C D _1 , … , D _k are domains of integration whose union is D and whose pairwise intersections have measure zero, then int_D f d V = int_ D _1 f d V + … + int_ D _k f d V. (d) If f ≥ 0 on D, then textstyle int _D f d V ≥ 0 , with equality if and only if f equiv 0 on Int D (e) beginarray r ( operatorname* i n f _D f ) V o l ( D ) le bar int _D f d V le ( operatorname* s u p _D f ) endarray Vol.D/. (f) beginarray r ∣ int _D f d V ∣ le int _D ∣ f ∣ d V endarray

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Mathlib’s Bochner/Lebesgue integral has linearity, positivity, null-set invariance, finite additivity, bounds, and the norm inequality, but the source theorem is explicitly about Lee’s Riemann integral. No formal equivalence layer was found. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Corollary C.25** {#fc08-cc-u035}

::: {.unit-meta}
`FC08-CC-U035` · Appendix C, § Multiple Integrals; source L19920 · [`mathlib`]{.route-mathlib}
:::

A set of measure zero in ℝ ^n contains no nonempty open subset.

::: {.unit-lean}
**In Lean.** [`Mathlib/MeasureTheory/Measure/OpenPos.lean::IsOpen.measure_pos, IsOpen.measure_pos_iff`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/OpenPos.html) — Lebesgue volume is positive on every nonempty open set, so a null set cannot contain a nonempty open subset; this is exactly Corollary C.25.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Theorem C.26** {#fc08-cc-u036}

::: {.unit-meta}
`FC08-CC-U036` · Appendix C, § Multiple Integrals; source L19926 · [`unmatched`]{.route-unmatched}
:::

(Change of Variables). Suppose D and E are open domains of integration in ℝ ^n , and G : bar(D) → bar(E) is smooth map that restricts to a diffeomorphism from D to E. For every continuous function f : bar(E) → ℝ int_E f d V = int_D (f ∘ G) ∣ det D G ∣ d V.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Mathlib has the stronger Lebesgue/Bochner Jacobian change-of-variables theorem `integral_image_eq_integral_abs_det_fderiv_smul`, but no checked equivalence to Lee’s Riemann integral on domains of integration was found. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Theorem C.27** {#fc08-cc-u037}

::: {.unit-meta}
`FC08-CC-U037` · Appendix C, § Multiple Integrals; source L19932 · [`unmatched`]{.route-unmatched}
:::

(Fubini’s Theorem). Let A = [ a ^1 , b ^1 ] × ·s × [ a ^n , b ^n ] be a closed rectangle in ℝ ^n , and let f : A → ℝ be continuous. Then int_A f d V = int_a ^n ^ b ^n (… (int_a ^1 ^ b ^1 f (x ^1, … , x ^n) d x ^1 ) … ) d x ^n, and the same is true if the variables in the iterated integral on the right-hand side are reordered in any way.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Mathlib’s [`MeasureTheory.integral_prod`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.integral_prod#doc) is the general Bochner Fubini theorem, but the canonical row states equality for Lee’s Riemann integral on rectangles. Without a checked Riemann–Lebesgue bridge, the stronger theorem is adjacent rather than an exact route. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Definition/convention — integral of F** {#fc08-cc-u038}

::: {.unit-meta}
`FC08-CC-U038` · Appendix C, § Integrals of Vector-Valued Functions; source L19942 · [`unmatched`]{.route-unmatched}
:::

If D ⊆ ℝ ^n is a domain of integration and F : D → ℝ ^k is a bounded continuous vector-valued function, we define the integral of F over D to be the vector in ℝ ^k obtained by integrating F component by component: int_D F d V = (int_D F ^1 d V, … , int_D F ^k d V ).

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Mathlib’s Bochner integral is intrinsically vector-valued and its coordinate projections commute with integration, but Lee defines a vector-valued Riemann integral componentwise. No checked equivalence between the underlying scalar integrals was found. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Proposition C.28** {#fc08-cc-u039}

::: {.unit-meta}
`FC08-CC-U039` · Appendix C, § Integrals of Vector-Valued Functions; source L19950 · [`unmatched`]{.route-unmatched}
:::

Suppose D ⊆ ℝ ^n is a domain of integration and F : D → ℝ ^k is a bounded continuous vector-valued function. Then ∣ int_D F d V ∣ ≤ int_D ∣ F ∣ d V.tagC.14

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — `norm_integral_le_integral_norm` proves the stronger Bochner inequality, but the canonical statement uses the preceding vector-valued Riemann integral. No checked bridge identifies them. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Proposition C.29** {#fc08-cc-u040}

::: {.unit-meta}
`FC08-CC-U040` · Appendix C, § Integrals of Vector-Valued Functions; source L19972 · [`unmatched`]{.route-unmatched}
:::

(Lipschitz Estimate for C ^1 Functions). Let U ⊆ ℝ ^n be an open subset, and suppose F : U ℝ ^m is of class C ^1 . Then F is Lipschitz continuous on every compact convex subset K ⊆ U . The Lipschitz constant can be taken to be textstyle operatorname* s u p _x ∈ K ∣ D F ( x ) ∣

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Mathlib proves that `C¹` maps on compact convex sets are Lipschitz and that any uniform derivative bound is a valid Lipschitz constant. The source additionally specifies the exact constant `sup_K ‖DF‖`; no single checked theorem with that bundled constant was found. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Corollary C.30** {#fc08-cc-u041}

::: {.unit-meta}
`FC08-CC-U041` · Appendix C, § Integrals of Vector-Valued Functions; source L19990 · [`mathlib`]{.route-mathlib}
:::

I f U ⊆ ℝ ^n is an open subset and F : U ℝ ^m is of class C ^1 , then f is locally Lipschitz continuous.

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/ContDiff/RCLike.lean::ContDiff.locallyLipschitz, ContDiffOn.locallyLipschitzOn`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/ContDiff/RCLike.html) — Mathlib directly proves that a `C¹` real map is locally Lipschitz (and the corresponding within-set statement on convex domains), exactly Corollary C.30.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Theorem C.31** {#fc08-cc-u042}

::: {.unit-meta}
`FC08-CC-U042` · Appendix C, § Sequences and Series of Functions; source L19998 · [`unmatched`]{.route-unmatched}
:::

(Properties of Uniform Convergence). Let S ⊆ ℝ ^n , and suppose f _i : S → ℝ ^m is continuous for each integer i ≥ 1 (a) I f f _i → f uniformly, then f is continuous. (b) If the sequence ( f _i ) _i = 1 ^∞ is uniformly Cauchy, then it converges uniformly to a continuous function. (c) If f _i → f uniformly and S is a compact domain of integration, then lim _i → ∞ int_S f _i d V = int_S f d V. (d) If S is open, each f is of class C ^1 , f _i → f pointwise, and ( ∂ f _i / ∂ x ^j ) converges uniformly on S as i → ∞ , then ∂ f / ∂ x ^j exists on S and (∂ f)/(∂ x ^j) = lim _i → ∞ (∂ f _i)/(∂ x ^j). For a proof, see [Apo74, Rud76, Str00]. Given an infinite series of (real-valued or vector-valued) functions textstyle sum _i = 0 ^∞ f _i on S ⊆ ℝ ^n , one says the series converges pointwise if the corresponding sequence of partial sums converges pointwise to some function f : : f (x) = lim _N arrow ∞ sum_i = 0 ^N f _i (x) text for all x ∈ S. We say the series converges uniformly if its partial sums do so.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Mathlib separately has uniform-limit continuity, completeness/uniform Cauchy convergence, integral convergence, smooth-series derivative convergence, and uniform-series notions, but this row bundles all four claims with the source Riemann integral/partial-derivative interfaces plus series terminology. No checked whole-row owner survives strict semantics. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Proposition C.32** {#fc08-cc-u043}

::: {.unit-meta}
`FC08-CC-U043` · Appendix C, § Sequences and Series of Functions; source L20026 · [`mathlib`]{.route-mathlib}
:::

(Weierstrass M -test). Suppose S ⊆ ℝ ^n , and f _i : S → ℝ ^k are functions. If there exist positive real numbers M _i such that operatorname* s u p _S ∣ f _i ∣ ≤ M _i and textstyle sum _i M _i converges, then textstyle sum _i f converges uniformly on S .

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Normed/Group/FunctionSeries.lean::tendstoUniformlyOn_tsum_nat, tendstoUniformly_tsum_nat`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Group/FunctionSeries.html) — Mathlib’s uniform-series M-test states that a summable scalar majorant bounding every summand norm yields uniform convergence of the series, exactly Proposition C.32.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Theorem C.34** {#fc08-cc-u044}

::: {.unit-meta}
`FC08-CC-U044` · Appendix C, § The Inverse and Implicit Function Theorems; source L20034 · [`mathlib`]{.route-mathlib}
:::

(Inverse Function Theorem). Suppose U and V are open subsets of ℝ ^n , and F : U → V is a smooth function. If D F ( a ) is invertible at some point a ∈ U , then there exist connected neighborhoods U _0 ⊆ U of a and V _0 ⊆ V of F ( a ) such that F ∣ _ U _0 : U _0 → V _0 is a diffeomorphism.

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean::HasStrictFDerivAt.toOpenPartialHomeomorph, HasStrictFDerivAt.to_localInverse`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.html); [`Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean::ContDiffAt.localInverse, ContDiffAt.to_localInverse`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.html) — Mathlib’s inverse function theorem gives mutually inverse maps on open neighborhoods when the derivative is a continuous linear equivalence; the `ContDiff` version gives the same smoothness to the inverse. In Euclidean space the neighborhoods can be shrunk to connected balls and their images, yielding Lee C.34.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Definition/convention — a contraction** {#fc08-cc-u045}

::: {.unit-meta}
`FC08-CC-U045` · Appendix C, § The Inverse and Implicit Function Theorems; source L20038 · [`mathlib`]{.route-mathlib}
:::

Let X be a metric space. A map G : X → X is said to be a contraction if there is a constant λ ∈ ( 0 , 1 ) such that d ( G ( x ) , G ( y ) ) ≤ λ d ( x , y ) for all x , y ∈ X . Clearly, every contraction is continuous. A fixed point of a map G : X → X is a point x ∈ X such that G ( x ) = x

::: {.unit-lean}
**In Lean.** [`Mathlib/Topology/MetricSpace/Contracting.lean::ContractingWith, ContractingWith.toLipschitzWith, ContractingWith.fixedPoint, ContractingWith.fixedPoint_isFixedPt, ContractingWith.fixedPoint_unique`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Contracting.html) — `ContractingWith K G` is `K<1` plus the Lipschitz inequality, hence continuity; on a nonempty complete metric space `fixedPoint` exists, is fixed, and `fixedPoint_unique` proves uniqueness. This is exactly Lee’s contraction definition and Lemma C.35.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Lemma C.35** {#fc08-cc-u046}

::: {.unit-meta}
`FC08-CC-U046` · Appendix C, § The Inverse and Implicit Function Theorems; source L20040 · [`mathlib`]{.route-mathlib}
:::

(Contraction Lemma). Let X be a nonempty complete metric space. Every contraction G : X → X has a unique fixed point.

::: {.unit-lean}
**In Lean.** [`Mathlib/Topology/MetricSpace/Contracting.lean::ContractingWith, ContractingWith.toLipschitzWith, ContractingWith.fixedPoint, ContractingWith.fixedPoint_isFixedPt, ContractingWith.fixedPoint_unique`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Contracting.html) — `ContractingWith K G` is `K<1` plus the Lipschitz inequality, hence continuity; on a nonempty complete metric space `fixedPoint` exists, is fixed, and `fixedPoint_unique` proves uniqueness. This is exactly Lee’s contraction definition and Lemma C.35.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Corollary C.36** {#fc08-cc-u047}

::: {.unit-meta}
`FC08-CC-U047` · Appendix C, § The Inverse and Implicit Function Theorems; source L20146 · [`unmatched`]{.route-unmatched}
:::

Suppose U ⊆ ℝ ^n is an open subset, and F : U → ℝ ^n is a smooth function whose Jacobian determinant is nonzero at every point in U (a) F is an open map. (b) If F is injective, then F : U → F ( U ) is a diffeomorphism.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — The inverse function theorem plus the line-derivative Jacobian assembly gives the mathematical proof, but no checked theorem packages Lee’s nonzero-Jacobian-everywhere hypotheses with both openness and the global injective-diffeomorphism conclusion. Reconstructing it would be substantive. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Example C.37** {#fc08-cc-u048}

::: {.unit-meta}
`FC08-CC-U048` · Appendix C, § The Inverse and Implicit Function Theorems; source L20156 · after [`FC08-CC-U047`](#fc08-cc-u047) · [`mathlib`]{.route-mathlib}
:::

(Polar Coordinates). As you know from calculus, polar coordinates ( r , θ ) in the plane are defined implicitly by the relations x = r cos θ y = r sin θ . The map F : ( 0 , ∞ ) × ℝ → ℝ ^2 defined by F ( r , θ ) = ( r cos θ , r sin θ ) is smooth and has Jacobian determinant equal to r , which is nonzero everywhere on the domain. Thus, Corollary C.36 shows that the restriction of F to any open subset on which it is injective is a diffeomorphism onto its image. One such subset is ( r , θ ) : r > 0 , - π < θ < π , which is mapped bijectively by F onto the complement of the nonpositive part of the x-axis. //

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/SpecialFunctions/PolarCoord.lean::polarCoord, continuous_polarCoord_symm, fderivPolarCoordSymm, det_fderivPolarCoordSymm`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/PolarCoord.html) — Mathlib’s `polarCoord` is an open partial homeomorphism between the slit plane and `(0,∞)×(-π,π)`; its inverse is `(r,θ) ↦ (r cos θ,r sin θ)`, and Mathlib computes its derivative determinant to be `r`. This realizes the complete polar-coordinate example.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Example C.38** {#fc08-cc-u049}

::: {.unit-meta}
`FC08-CC-U049` · Appendix C, § The Inverse and Implicit Function Theorems; source L20158 · [`unmatched`]{.route-unmatched}
:::

(Spherical Coordinates). Similarly, spherical coordinates on ℝ ^3 are the functions ( ρ , φ , θ ) / defined by the relations x = ρ sin φ cos θ , y = ρ sin φ sin θ , z = ρ cos φ . Thus, the restriction of G to any open subset on which it is injective is a diffeomorphism onto its image. If we define G : ( 0 , ∞ ) × ( 0 , π ) × ℝ → ℝ ^3 by G ( ρ , φ , θ ) = ( ρ sin ' cos θ; ρ sin ' sin θ , ρ cos φ ) a computation shows that the Jacobian determinant of G is ρ ^2 sin φ ≠ 0 . One such subset is (ρ , φ , θ): ρ > 0, 0 < φ < π , - π < θ < π . Notice how much easier it is to argue this way than to try to construct an inverse map explicitly out of inverse trigonometric functions.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — Targeted P/H and external searches found no spherical-coordinate partial diffeomorphism with the full formula, determinant `ρ² sin φ`, and stated injectivity region. Polar coordinates are formalized, but the 3-dimensional example is not inferred from analogy. Strict whole-row semantics reject proper subsets, unverified representation bridges, and substantive reconstruction from adjacent generic ingredients.
:::

### **Theorem C.40** {#fc08-cc-u050}

::: {.unit-meta}
`FC08-CC-U050` · Appendix C, § The Inverse and Implicit Function Theorems; source L20184 · [`mathlib`]{.route-mathlib}
:::

(Implicit Function Theorem). Let U ⊆ ℝ ^n × ℝ ^k be an open subset, and let ( x , y ) = ( x ^1 , … , x ^n , y ^1 , … , y ^k ) denote the standard coordinates on U . Suppose φ : U → ℝ ^k is a smooth function, ( a , b ) ∈ U , and c = varPhi ( a , b ) . If the k × k matrix ((∂ Phi^i)/(∂ y ^j) (a, b) ) is nonsingular, then there exist neighborhoods V _0 ⊆ ℝ ^n of a and W _0 ⊆ ℝ ^k of b and a smooth function F : V _0 W _0 such that φ ^- 1 ( c ) ∩ ( V _0 × W _0 ) is the graph of F , that is, beginarray r φ ( x , y ) = c f o r ( x , y ) ∈ V _0 × W _0 endarray if and only i f y = F ( x )

::: {.unit-lean}
**In Lean.** [`Mathlib/Analysis/Calculus/ImplicitContDiff.lean::ContDiffAt.implicitFunction, ContDiffAt.eventually_apply_implicitFunction, ContDiffAt.eventually_apply_eq_iff_implicitFunction, ContDiffAt.contDiffAt_implicitFunction`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/ImplicitContDiff.html) — Mathlib’s product-domain implicit-function theorem constructs a local `C^n` implicit function when the derivative in the second factor is invertible and proves the local level-set iff graph equation, exactly Lee C.40 after identifying the partial derivative block with the corresponding restriction of `fderiv`.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}


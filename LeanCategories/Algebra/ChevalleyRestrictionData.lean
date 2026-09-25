/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Chevalley restriction data

Definition-level realization of Humphreys FC14-C06-U038.

For a subspace `H <= L`, restriction of linear functionals
`L* -> H*` extends by the symmetric-algebra universal property to the
polynomial restriction homomorphism `P(L) -> P(H)`.

Humphreys restricts this homomorphism further to
`P(L)^G -> P(H)^W`, where `G = Int(L)` and `W` is the Weyl group.
Landing in the invariant codomain is a theorem: it uses representatives of
Weyl reflections by inner automorphisms.  Sweep III therefore records the
exact graph of that restricted map.  Its output already ranges over
`P(H)^W`; no arbitrary polynomial or weakened ambient codomain is used.
The result layer proves that the graph is total for the source actions.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v w x

/-- Polynomial functions on a vector space, in Humphreys' convention
`P(V) = S(V*)`. -/
abbrev PolynomialFunctionData
    (K : Type u) (V : Type v) [CommSemiring K] [AddCommMonoid V] [Module K V] :=
  SymmetricAlgebra K (Module.Dual K V)

/-- The raw restriction homomorphism `P(L) -> P(H)` induced by the inclusion
`H -> L`. -/
def polynomialRestrictionData
    (K : Type u) {L : Type v} [CommSemiring K] [AddCommMonoid L] [Module K L]
    (H : Submodule K L) :
    PolynomialFunctionData K L →ₐ[K] PolynomialFunctionData K H :=
  SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι K (Module.Dual K H)).comp H.dualRestrict)

/-- Invariant polynomial functions for a supplied source group action.

For FC14-C06-U038 the two instances are the `Int(L)` action on `P(L)`
and the Weyl-group action on `P(H)` already routed by FC14-C06-U036. -/
abbrev InvariantPolynomialData
    (G : Type w) (K : Type u) (V : Type v)
    [CommSemiring K] [AddCommMonoid V] [Module K V]
    [Monoid G] [MulSemiringAction G (PolynomialFunctionData K V)]
    [SMulCommClass G K (PolynomialFunctionData K V)] :=
  FixedPoints.subalgebra K (PolynomialFunctionData K V) G

/-- Exact graph of Chevalley restriction on invariant polynomials.

The candidate output is already a `W`-fixed polynomial.  The equation says
that, after forgetting invariant-subalgebra membership, it is exactly the raw
restriction of the given `G`-fixed polynomial.  The source theorem that
restriction of every `G`-fixed polynomial is `W`-fixed is exactly the
totality statement for this graph and remains result-layer content. -/
def IsChevalleyRestrictionValueData
    {K : Type u} {L : Type v} {G : Type w} {W : Type x}
    [CommSemiring K] [AddCommMonoid L] [Module K L]
    [Monoid G] [MulSemiringAction G (PolynomialFunctionData K L)]
    [SMulCommClass G K (PolynomialFunctionData K L)]
    (H : Submodule K L)
    [Monoid W] [MulSemiringAction W (PolynomialFunctionData K H)]
    [SMulCommClass W K (PolynomialFunctionData K H)]
    (p : InvariantPolynomialData G K L)
    (q : InvariantPolynomialData W K H) : Prop :=
  (q : PolynomialFunctionData K H) =
    polynomialRestrictionData K H (p : PolynomialFunctionData K L)

/-- Graph predicate for a proposed Chevalley restriction function.

No existence claim is bundled: proving this predicate for a function is the
result-layer invariance step supplied by Weyl representatives in `Int(L)`. -/
def IsChevalleyRestrictionData
    {K : Type u} {L : Type v} {G : Type w} {W : Type x}
    [CommSemiring K] [AddCommMonoid L] [Module K L]
    [Monoid G] [MulSemiringAction G (PolynomialFunctionData K L)]
    [SMulCommClass G K (PolynomialFunctionData K L)]
    (H : Submodule K L)
    [Monoid W] [MulSemiringAction W (PolynomialFunctionData K H)]
    [SMulCommClass W K (PolynomialFunctionData K H)]
    (theta : InvariantPolynomialData G K L → InvariantPolynomialData W K H) : Prop :=
  ∀ p, IsChevalleyRestrictionValueData H p (theta p)

end LeanCategories.Algebra

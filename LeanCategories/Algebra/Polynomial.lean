/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder

@[expose] public section

/-!
# Groebner bases

Mathlib supplies monomial orders, leading terms, reduction, division, and
S-polynomials. This file defines the Groebner-basis predicate, adapted from
`WuProver/groebner_proj`, `Groebner/Groebner.lean`:
https://github.com/WuProver/groebner_proj/blob/42910339be485d279407382576e767223898c543/Groebner/Groebner.lean
-/

namespace MonomialOrder

/-- A set is a Groebner basis for an ideal when its leading terms generate the
leading-term ideal of that ideal. -/
def IsGroebnerBasis {σ : Type*} {m : MonomialOrder σ} {R : Type*}
    [CommSemiring R] (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) : Prop :=
  G ⊆ I ∧ Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R))) =
    Ideal.span (m.leadingTerm '' G)

end MonomialOrder

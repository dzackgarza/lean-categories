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
S-polynomials. This file supplies the reusable predicates needed for the
foundational-corpus Groebner layer. The Groebner-basis, remainder, minimality,
and reducedness interfaces are adapted from `WuProver/groebner_proj` at
revision `42910339be485d279407382576e767223898c543` (Apache-2.0).
-/

namespace MonomialOrder

open MvPolynomial

/-- A set is a Groebner basis for an ideal when its leading terms generate the
leading-term ideal of that ideal. -/
def IsGroebnerBasis {σ : Type*} {m : MonomialOrder σ} {R : Type*}
    [CommSemiring R] (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) : Prop :=
  G ⊆ I ∧ Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R))) =
    Ideal.span (m.leadingTerm '' G)

/-- `r` is a remainder of `f` on division by the set `B` with respect to `m`
when `f-r` is a finite `B`-combination whose summands do not exceed the degree
of `f`, and no monomial of `r` is divisible by a leading monomial from `B`.
This is the relational form of the output contract of `MonomialOrder.div_set`. -/
def IsRemainder {σ : Type*} (m : MonomialOrder σ) {R : Type*} [CommRing R]
    (f : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) : Prop :=
  (∃ g : B →₀ MvPolynomial σ R,
      f = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ R)) g + r ∧
      ∀ b : B, m.degree ((b : MvPolynomial σ R) * g b) ≼[m] m.degree f) ∧
    ∀ c ∈ r.support, ∀ b ∈ B, ¬m.degree b ≤ c

/-- One deterministic step of multivariate division by an ordered finite family.
The first divisor whose leading monomial divides the current leading monomial
is used; if no divisor applies, the current leading term is moved to the
remainder accumulator. -/
def OrderedDivisionStep {σ : Type*} (m : MonomialOrder σ) {k : Type*} [Field k]
    {n : ℕ} (b : Fin n → MvPolynomial σ k) :
    (MvPolynomial σ k × MvPolynomial σ k) →
      (MvPolynomial σ k × MvPolynomial σ k) → Prop :=
  fun state next =>
    (∃ i : Fin n,
      b i ≠ 0 ∧ m.degree (b i) ≤ m.degree state.1 ∧
      (∀ j : Fin n, j < i → b j = 0 ∨ ¬m.degree (b j) ≤ m.degree state.1) ∧
      next =
        (state.1 -
          monomial (m.degree state.1 - m.degree (b i))
            ((m.leadingCoeff (b i))⁻¹ * m.leadingCoeff state.1) * b i, state.2)) ∨
    (state.1 ≠ 0 ∧
      (∀ i : Fin n, b i = 0 ∨ ¬m.degree (b i) ≤ m.degree state.1) ∧
      next = (state.1 - m.leadingTerm state.1, state.2 + m.leadingTerm state.1))

/-- Data carried by the source ordered multivariate-division procedure.

`current` is the polynomial still to be reduced, `quotients i` is the
coefficient accumulated at the `i`th divisor, and `remainder` is the
accumulated remainder. Divisor positions are retained, so repeated equal
polynomials remain distinct entries exactly as in the ordered source list
(FC01-C09-U052). -/
structure OrderedDivisionState (σ : Type*) (k : Type*) [Field k] (n : ℕ) where
  current : MvPolynomial σ k
  quotients : Fin n → MvPolynomial σ k
  remainder : MvPolynomial σ k

/-- The initial state of ordered multivariate division. -/
def orderedDivisionInitialState {σ : Type*} {k : Type*} [Field k] {n : ℕ}
    (f : MvPolynomial σ k) : OrderedDivisionState σ k n where
  current := f
  quotients := 0
  remainder := 0

/-- The first divisor position whose leading monomial divides the current
leading monomial. This is the source's ordered first-applicable-divisor
choice; no termination statement is part of this definition. -/
noncomputable def orderedDivisionFirstDivisor? {σ : Type*} (m : MonomialOrder σ)
    {k : Type*} [Field k] {n : ℕ} (b : Fin n → MvPolynomial σ k)
    (f : MvPolynomial σ k) : Option (Fin n) := by
  classical
  exact (List.finRange n).find? fun i =>
    decide (b i ≠ 0 ∧ m.degree (b i) ≤ m.degree f)

/-- The quotient monomial used when the `i`th divisor cancels the current
leading term. -/
noncomputable def orderedDivisionQuotientTerm {σ : Type*} (m : MonomialOrder σ)
    {k : Type*} [Field k] {n : ℕ} (b : Fin n → MvPolynomial σ k)
    (state : OrderedDivisionState σ k n) (i : Fin n) : MvPolynomial σ k :=
  monomial (m.degree state.current - m.degree (b i))
    ((m.leadingCoeff (b i))⁻¹ * m.leadingCoeff state.current)

/-- One deterministic data step of Dummit--Foote's ordered multivariate
division algorithm (FC01-C09-U052).

If an ordered divisor applies, the first such position is used and its
positional quotient accumulator is increased. Otherwise the current leading
term is moved to the remainder. Termination and every equation satisfied by
the eventual output are result-layer statements. -/
noncomputable def orderedDivisionDataStep {σ : Type*} (m : MonomialOrder σ)
    {k : Type*} [Field k] {n : ℕ} (b : Fin n → MvPolynomial σ k)
    (state : OrderedDivisionState σ k n) : OrderedDivisionState σ k n := by
  classical
  match orderedDivisionFirstDivisor? m b state.current with
  | some i =>
      let q := orderedDivisionQuotientTerm m b state i
      exact
        { current := state.current - q * b i
          quotients := Function.update state.quotients i (state.quotients i + q)
          remainder := state.remainder }
  | none =>
      exact
        { current := state.current - m.leadingTerm state.current
          quotients := state.quotients
          remainder := state.remainder + m.leadingTerm state.current }

/-- The complete quotient/remainder state after a specified number of source
division steps. This fuelled construction keeps Sweep III free of the
well-founded termination proof. -/
noncomputable def orderedDivisionStateAfter {σ : Type*} (m : MonomialOrder σ)
    {k : Type*} [Field k] {n : ℕ} (b : Fin n → MvPolynomial σ k)
    (f : MvPolynomial σ k) (steps : ℕ) : OrderedDivisionState σ k n :=
  (orderedDivisionDataStep m b)^[steps] (orderedDivisionInitialState f)

/-- `r` is the remainder produced by the textbook ordered multivariate-division
procedure applied to `f` and the ordered divisor family `b`.  This is the
definition-level relation underlying the ordered division algorithm FC01-C09-U052;
FC01-C09-U057 is only the notation `f ≡ r mod G` for this output relation.
Termination and comparison with Gröbner normal forms are theorem-level facts. -/
def IsOrderedRemainder {σ : Type*} (m : MonomialOrder σ) {k : Type*} [Field k]
    {n : ℕ} (b : Fin n → MvPolynomial σ k)
    (f r : MvPolynomial σ k) : Prop :=
  Relation.ReflTransGen (m.OrderedDivisionStep b) (f, 0) (0, r)

namespace IsGroebnerBasis

variable {σ R : Type*} [CommRing R] {m : MonomialOrder σ}
variable {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}

/-- A Groebner basis is minimal when it is monic and no leading monomial of one
basis element divides the leading monomial of another. -/
def IsMinimal (_hG : m.IsGroebnerBasis G I) : Prop :=
  (∀ p ∈ G, m.Monic p) ∧
    ∀ p ∈ G, ∀ q ∈ G, q ≠ p → ¬m.degree q ≤ m.degree p

/-- A Groebner basis is reduced when it is monic and every basis element is
already a remainder modulo the other basis elements. -/
def IsReduced (_hG : m.IsGroebnerBasis G I) : Prop :=
  (∀ p ∈ G, m.Monic p) ∧ ∀ p ∈ G, m.IsRemainder p (G \ {p}) p

/-- Replace each element of a minimal Gröbner basis by a chosen remainder on
division by the other basis elements.  The reference implementation proves
that this image is a reduced Gröbner basis; that theorem belongs to Sweep IV.
This is the construction in Dummit--Foote FC01-C09-U062. -/
def IsMinimal.reduceByRemainders {hG : m.IsGroebnerBasis G I}
    (_hmin : hG.IsMinimal) (r : G → MvPolynomial σ R)
    (_hr : ∀ g : G, m.IsRemainder g.1 (G \ {g.1}) (r g)) : Set (MvPolynomial σ R) :=
  Set.range r

end IsGroebnerBasis

end MonomialOrder

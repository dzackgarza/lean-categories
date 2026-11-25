/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Card
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

/-!
# `E-HAT-2.1-25`: the sign identity behind the barycentric subdivision formula

Card `E-HAT-2.1-25` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 2.1, exercise 25.  Certificate: new-qual-site
`proofs/cards/BarySign.lean` at commit `16c09abaa4`.

Hatcher defines the subdivision operator by `S λ = b_λ (S ∂λ)`, which prepends the barycentre
of the whole simplex.  Expanding that recursion, the summands are indexed by permutations `π`
of the vertices, and the sign of the `π`-summand is `(-1)` to the power *the sum of the
deletion positions along the descending chain*: going down from the full simplex, the vertex
deleted at the stage where the current face has vertex set `F` contributes its position among
the vertices of `F` below it.

The combinatorial content of the correction is that this exponent plus the number of
inversions is the total number of pairs, `N (N - 1) / 2` where `N = n + 1` is the number of
vertices, so the recursion's sign is `(-1)^{N(N-1)/2} · sgn(π)`.

This file proves the counting and sign algebra for every `N`.  The recursion itself, and the
identification of its deletion positions with the counted noninversions, are in
`LeanCategories.Topology.BarySubdiv`.

LC-09 search record (formalization corpus, several formulations).  The sign-as-a-product
identity is Mathlib's `Equiv.Perm.sign_eq_prod_prod_Iio`, used here directly; the counting
lemmas are not in Mathlib.  The corpus's nearest hit is TauCeti
`TauCeti/GroupTheory/Perm/Inversion.lean`, whose `TauCeti.sign_eq_neg_one_pow_card_inversion`
states the same identity for its own `Finset.inversions` (pairs `i < j` with `σ j < σ i`) and
whose `TauCeti.Data.Finset.Inversions` supplies that count.  That file is not importable here
and counts a `Finset (Fin n × Fin n)` of nondependent pairs, whereas the recursion of
`BarySubdiv` needs the sigma-finset `pairSet` and its `Finset.card_sigma` computation; the
port below keeps the certificate's formulation and proof.  Queries run:
`content:sign_eq_neg_one_pow_inv`, `permutation sign inversions cardinality`,
`content:Equiv.Perm.sign_eq_prod_prod_Iio`, `content:Finset.inversions`,
`card_filter_add_card_filter_not`.

Provenance: ported from new-qual-site at commit `16c09abaa4`, `proofs/cards/BarySign.lean`;
theorem names keep the certificate's spelling.
-/

open scoped BigOperators

namespace LeanCategories.Topology.BarySign

/-- The set of pairs `i < j` in `Fin N`, as a finset of dependent pairs. -/
def pairSet (N : ℕ) : Finset (Sigma fun _ : Fin N => Fin N) :=
  Finset.univ.sigma fun j => Finset.Iio j

theorem card_pairSet (N : ℕ) : (pairSet N).card = N * (N - 1) / 2 := by
  rw [pairSet, Finset.card_sigma]
  have h : ∀ j : Fin N, (Finset.Iio j).card = j.val := fun j => Fin.card_Iio j
  rw [Finset.sum_congr rfl (fun j _ => h j), Fin.sum_univ_eq_sum_range (fun i => i) N,
    Finset.sum_range_id]

/-- The number of noninversions: pairs `i < j` with `π i < π j`, which is the number counted
by the deletion positions of the descending chain. -/
def noninv {N : ℕ} (π : Equiv.Perm (Fin N)) : ℕ :=
  (pairSet N).filter (fun p => π p.2 < π p.1) |>.card

/-- The number of inversions. -/
def inv {N : ℕ} (π : Equiv.Perm (Fin N)) : ℕ :=
  (pairSet N).filter (fun p => ¬ π p.2 < π p.1) |>.card

/-- Inversions and noninversions partition the pairs. -/
theorem noninv_add_inv {N : ℕ} (π : Equiv.Perm (Fin N)) :
    noninv π + inv π = N * (N - 1) / 2 := by
  rw [noninv, inv, Finset.card_filter_add_card_filter_not, card_pairSet]

/-- The maintained sign formula: `sgn π` is the product over pairs `i < j` of `1` at a
noninversion and `-1` at an inversion. -/
theorem sign_eq_prod {N : ℕ} (π : Equiv.Perm (Fin N)) :
    π.sign = ∏ j, ∏ i ∈ Finset.Iio j, (if π i < π j then (1 : ℤˣ) else -1) :=
  π.sign_eq_prod_prod_Iio

/-- The same product as a single product over the pair set. -/
theorem sign_eq_prod_pairSet {N : ℕ} (π : Equiv.Perm (Fin N)) :
    π.sign = ∏ p ∈ pairSet N, (if π p.2 < π p.1 then (1 : ℤˣ) else -1) := by
  rw [sign_eq_prod, pairSet, Finset.prod_sigma']

/-- A product of signs over any set of pairs is `-1` to the number of inverted pairs. -/
theorem prod_ite_neg_one {N : ℕ} (π : Equiv.Perm (Fin N))
    (s : Finset (Sigma fun _ : Fin N => Fin N)) :
    (∏ p ∈ s, (if π p.2 < π p.1 then (1 : ℤˣ) else -1))
      = (-1 : ℤˣ) ^ (s.filter (fun p => ¬ π p.2 < π p.1)).card := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.filter_insert]
      by_cases h : π a.2 < π a.1
      · rw [ite_eq_left h, ite_eq_right (by simp [h]), one_mul]
      · rw [ite_eq_right h, ite_eq_left h, Finset.card_insert_of_notMem (by simp [ha]), pow_succ,
          mul_comm]

/-- And therefore `sgn π = (-1)^{inv π}`. -/
theorem sign_eq_neg_one_pow_inv {N : ℕ} (π : Equiv.Perm (Fin N)) :
    π.sign = (-1 : ℤˣ) ^ inv π := by
  rw [sign_eq_prod_pairSet, prod_ite_neg_one, inv]

/-- **The correspondence.** The exponent of Hatcher's recursion is the sum, over the stages
of the descending chain, of the position of the deleted vertex in the current face.  Going
from the face `F_j = {π 0, …, π j}` down to `F_{j-1}` the deleted vertex is `π j`, whose
position among the vertices of `F_j` is the number of `i ≤ j` with `π i < π j`.  So the
recursion's exponent is `delSum π` below. -/
def delSum {N : ℕ} (π : Equiv.Perm (Fin N)) : ℕ :=
  ∑ j : Fin N, ((Finset.Iic j).filter fun i => π i < π j).card

/-- The diagonal contributes nothing, so the position can be counted with `i < j`. -/
theorem filter_Iic_eq_filter_Iio {N : ℕ} (π : Equiv.Perm (Fin N)) (j : Fin N) :
    (Finset.Iic j).filter (fun i => π i < π j) = (Finset.Iio j).filter (fun i => π i < π j) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Iio]
  constructor
  · rintro ⟨hle, hlt⟩
    rcases lt_or_eq_of_le hle with h' | h'
    · exact ⟨h', hlt⟩
    · subst h'
      exact absurd hlt (lt_irrefl _)
  · rintro ⟨hlt, hlt'⟩
    exact ⟨le_of_lt hlt, hlt'⟩

/-- The pair set filters through the sigma structure. -/
theorem filter_pairSet {N : ℕ} (π : Equiv.Perm (Fin N)) :
    (pairSet N).filter (fun p => π p.2 < π p.1)
      = Finset.univ.sigma (fun j : Fin N => (Finset.Iio j).filter (fun i => π i < π j)) := by
  ext p
  obtain ⟨j, i⟩ := p
  simp [pairSet, Finset.mem_sigma, Finset.mem_filter]

/-- **The deletion-index correspondence.** The recursion's exponent is the number of
noninversions. -/
theorem delSum_eq_noninv {N : ℕ} (π : Equiv.Perm (Fin N)) : delSum π = noninv π := by
  rw [delSum, noninv, filter_pairSet, Finset.card_sigma]
  exact Finset.sum_congr rfl fun j _ => by rw [filter_Iic_eq_filter_Iio]

/-- **The all-`n` sign identity.** The recursion's sign `(-1)^{delSum π}` is
`(-1)^{N(N-1)/2} sgn(π)`. -/
theorem pow_delSum_eq_global_mul_sign {N : ℕ} (π : Equiv.Perm (Fin N)) :
    (-1 : ℤˣ) ^ (delSum π) = (-1 : ℤˣ) ^ (N * (N - 1) / 2) * π.sign := by
  have hT : N * (N - 1) / 2 = delSum π + inv π := by
    rw [← noninv_add_inv π, delSum_eq_noninv π]
  rw [sign_eq_neg_one_pow_inv, hT, pow_add]
  have h2 : ((-1 : ℤˣ) ^ inv π) * ((-1 : ℤˣ) ^ inv π) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [mul_assoc, h2, mul_one]

end LeanCategories.Topology.BarySign

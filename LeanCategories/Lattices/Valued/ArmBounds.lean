/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DiagramBounds
public import Mathlib.NumberTheory.ADEInequality

/-!
# The arm length bound on the diagram of a base of simple roots

`DiagramBounds.lean` bounds the shape of the graph of a base: it is acyclic, of degree at most
three, and a connected component carries at most one vertex of degree three. So a connected
diagram is a path or a star with three arms. This file supplies the numerical bound on the
lengths of those arms.

* `IsArm` names the pairing pattern of a run of vectors `x 0, x 1, …, x (n-1)` along an arm:
  each has self-pairing `-2`, consecutive ones pair to `1`, and non-consecutive ones pair to
  `0`. `armVector` is the weighted sum `∑ i < n, (i + 1) • x i`. The index runs from the far
  end of the arm inwards, so `x 0` is the leaf and carries weight `1`, and `x (n-1)` is the
  neighbour of the branch node and carries weight `n`.
* `pairing_armVector_branch` is the computation against the branch node: a vector orthogonal to
  all of the arm except its inner end, where it pairs to `1`, pairs to `n` with `armVector`.
  The lemma is stated for an arbitrary such vector, because the induction that computes the
  self-pairing applies it with the next vector of the arm itself in that role.
* `pairing_armVector_self` is the self-pairing, `-n(n+1)`. Writing `p = n + 1` for the length of
  the arm counted with the branch node, the two values read `-p(p-1)` and `p - 1`.
* `arm_length_inequality_of_gram` is the bound, in the form that only mentions the Gram matrix
  of the configuration. For a branch node `c` and three pairwise orthogonal arm vectors, the
  combination `pqr • c + qr • A₀ + pr • A₁ + pq • A₂` has self-pairing
  `pqr * (pqr - (qr + pr + pq))`; the coefficients are the ones that make it the error term of
  the projection of `c` onto the span of the arms. Negative definiteness forces
  `pqr < qr + pr + pq`, which is the integer form of `1/p + 1/q + 1/r > 1`.
* `IsThreeArmStar` packages a branch node together with three arms of a base of simple roots,
  and `IsThreeArmStar.arm_length_inequality` is the bound for it. The one input beyond the
  Gram matrix is that the combination above is nonzero, and that comes from the base being a
  `ℤ`-basis: the coefficient of the branch node in it is `pqr ≠ 0`, so
  `IsRootBase.repr_armVector_eq_zero` and `IsRootBase.repr_basis_self` read it off.
* `IsThreeArmStar.admissible` is the classification consequence. Mathlib's
  `ADEInequality.admissible_of_one_lt_sumInv` enumerates the solutions of `1/p + 1/q + 1/r > 1`,
  so the arm lengths of a three-armed star of a base of an even negative definite lattice form
  one of the ADE triples: `(1, q, r)`, `(2, 2, r)`, `(2, 3, 3)`, `(2, 3, 4)` or `(2, 3, 5)`.

What is not here is the graph-theoretic step that produces the three arms of `IsThreeArmStar`
from a connected diagram with a branch node. `DiagramBounds.lean` locates the branch node; the
decomposition of the rest of the diagram into three paths out of it is a separate development.
Every statement below therefore takes the three arms as given.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

namespace FiniteProjectiveLatticeCat

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-! ## Arms and their weighted sums -/

/-- The pairing pattern of an arm of a diagram: a run `x 0, x 1, …, x (n-1)` of `n` vectors of
self-pairing `-2` in which consecutive vectors pair to `1` and all other pairs are orthogonal.
The index increases towards the branch node, so `x 0` is the far end of the arm. Only the
pairings inside the run are constrained, so `x` may be any extension of the run to `ℕ`. -/
structure IsArm (L : FiniteProjectiveLatticeCat ℤ ℤ) (x : ℕ → L.obj.obj.carrier) (n : ℕ) :
    Prop where
  /-- Every vector of the run is a root of the single level set `-2`. -/
  pairing_self : ∀ i, i < n → L.obj.obj.pairing (x i) (x i) = -2
  /-- Consecutive vectors of the run pair to `1`. -/
  pairing_succ : ∀ i, i + 1 < n → L.obj.obj.pairing (x i) (x (i + 1)) = 1
  /-- Non-consecutive vectors of the run are orthogonal. -/
  pairing_far : ∀ i j, i + 1 < j → j < n → L.obj.obj.pairing (x i) (x j) = 0

/-- An initial segment of an arm is an arm. -/
theorem IsArm.mono {x : ℕ → L.obj.obj.carrier} {m n : ℕ} (h : IsArm L x n) (hmn : m ≤ n) :
    IsArm L x m where
  pairing_self i hi := h.pairing_self i (lt_of_lt_of_le hi hmn)
  pairing_succ i hi := h.pairing_succ i (lt_of_lt_of_le hi hmn)
  pairing_far i j hij hj := h.pairing_far i j hij (lt_of_lt_of_le hj hmn)

/-- The weighted sum along an arm, with weight `i + 1` at the vector of index `i`. The far end
of the arm carries weight `1` and the neighbour of the branch node carries weight `n`. -/
def armVector (L : FiniteProjectiveLatticeCat ℤ ℤ) (x : ℕ → L.obj.obj.carrier) (n : ℕ) :
    L.obj.obj.carrier :=
  ∑ i ∈ Finset.range n, ((i : ℤ) + 1) • x i

@[simp]
theorem armVector_zero (L : FiniteProjectiveLatticeCat ℤ ℤ) (x : ℕ → L.obj.obj.carrier) :
    L.armVector x 0 = 0 :=
  rfl

/-- Extending an arm by one vector adds it with the next weight. -/
theorem armVector_succ (L : FiniteProjectiveLatticeCat ℤ ℤ) (x : ℕ → L.obj.obj.carrier)
    (n : ℕ) : L.armVector x (n + 1) = L.armVector x n + ((n : ℤ) + 1) • x n :=
  Finset.sum_range_succ _ _

/-- The pairing of the weighted sum along an arm with a vector attached to its inner end. The
hypotheses are the ones the branch node of a diagram satisfies: orthogonality to every vector
of the arm except the last, and pairing `1` with that one. The value is the length of the arm,
independently of where the weights are placed elsewhere. -/
theorem pairing_armVector_branch (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {x : ℕ → L.obj.obj.carrier} {n : ℕ} {y : L.obj.obj.carrier}
    (hzero : ∀ i, i + 1 < n → L.obj.obj.pairing (x i) y = 0)
    (hone : ∀ i, i + 1 = n → L.obj.obj.pairing (x i) y = 1) :
    L.obj.obj.pairing (L.armVector x n) y = (n : ℤ) := by
  cases n with
  | zero => simp
  | succ m =>
    have h0 : L.obj.obj.pairing (L.armVector x m) y = 0 := by
      rw [armVector, pairing_sum_left]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi' : i < m := Finset.mem_range.mp hi
      rw [BilinModuleCat.pairing_zsmul_left, hzero i (by omega), smul_zero]
    rw [armVector_succ, BilinModuleCat.pairing_add_left, h0,
      BilinModuleCat.pairing_zsmul_left, hone m rfl, smul_eq_mul, mul_one, zero_add]
    push_cast
    ring

/-- The self-pairing of the weighted sum along an arm of `n` vectors is `-n(n + 1)`. Counting
the branch node the arm has length `p = n + 1`, so the value is `-p(p - 1)`.

Extending the arm by one vector adds `-2(n + 1)²` for the new diagonal term and `2(n + 1)n` for
the two new cross terms, the second by `pairing_armVector_branch` applied to the new vector. -/
theorem pairing_armVector_self (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (x : ℕ → L.obj.obj.carrier) :
    ∀ n : ℕ, IsArm L x n →
      L.obj.obj.pairing (L.armVector x n) (L.armVector x n) = -((n : ℤ) * ((n : ℤ) + 1)) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ m ih =>
    intro h
    have hcross : L.obj.obj.pairing (L.armVector x m) (x m) = (m : ℤ) :=
      pairing_armVector_branch L (fun i hi => h.pairing_far i m hi (by omega))
        (fun i hi => by
          have : x m = x (i + 1) := by rw [hi]
          rw [this]
          exact h.pairing_succ i (by omega))
    rw [armVector_succ, pairing_add_self, ih (h.mono (Nat.le_succ m)),
      BilinModuleCat.pairing_zsmul_right, hcross, BilinModuleCat.pairing_zsmul_left,
      BilinModuleCat.pairing_zsmul_right, h.pairing_self m (by omega)]
    simp only [smul_eq_mul]
    push_cast
    ring

/-! ## The bound from the Gram matrix of a star -/

/-- The arm length bound, in the form that mentions only the Gram matrix of the configuration.

`c` is the branch node and `A₀, A₁, A₂` are the weighted sums along three pairwise orthogonal
arms of lengths `p, q, r` counted with the branch node. The combination
`pqr • c + qr • A₀ + pr • A₁ + pq • A₂` clears the denominators of `c` minus its projection on
the span of the arms, and has self-pairing `pqr * (pqr - (qr + pr + pq))`. A nonzero vector of a
negative definite lattice has negative self-pairing, so `pqr < qr + pr + pq`. -/
theorem arm_length_inequality_of_gram (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsNegativeDefiniteLattice L) {c A₀ A₁ A₂ : L.obj.obj.carrier} {p q r : ℤ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hcc : L.obj.obj.pairing c c = -2)
    (h00 : L.obj.obj.pairing A₀ A₀ = -((p - 1) * p))
    (h11 : L.obj.obj.pairing A₁ A₁ = -((q - 1) * q))
    (h22 : L.obj.obj.pairing A₂ A₂ = -((r - 1) * r))
    (h0c : L.obj.obj.pairing A₀ c = p - 1)
    (h1c : L.obj.obj.pairing A₁ c = q - 1)
    (h2c : L.obj.obj.pairing A₂ c = r - 1)
    (h01 : L.obj.obj.pairing A₀ A₁ = 0)
    (h02 : L.obj.obj.pairing A₀ A₂ = 0)
    (h12 : L.obj.obj.pairing A₁ A₂ = 0)
    (hne : (p * q * r) • c + (q * r) • A₀ + (p * r) • A₁ + (p * q) • A₂ ≠ 0) :
    p * q * r < q * r + p * r + p * q := by
  have hc0 : L.obj.obj.pairing c A₀ = p - 1 := by rw [pairing_comm]; exact h0c
  have hc1 : L.obj.obj.pairing c A₁ = q - 1 := by rw [pairing_comm]; exact h1c
  have hc2 : L.obj.obj.pairing c A₂ = r - 1 := by rw [pairing_comm]; exact h2c
  have h10 : L.obj.obj.pairing A₁ A₀ = 0 := by rw [pairing_comm]; exact h01
  have h20 : L.obj.obj.pairing A₂ A₀ = 0 := by rw [pairing_comm]; exact h02
  have h21 : L.obj.obj.pairing A₂ A₁ = 0 := by rw [pairing_comm]; exact h12
  have hself := L.pairing_self_neg hL hne
  simp only [BilinModuleCat.pairing_add_left, BilinModuleCat.pairing_add_right,
    BilinModuleCat.pairing_zsmul_left, BilinModuleCat.pairing_zsmul_right, smul_eq_mul,
    hcc, h00, h11, h22, h0c, h1c, h2c, hc0, hc1, hc2, h01, h02, h12, h10, h20, h21] at hself
  nlinarith [mul_pos (mul_pos hp hq) hr, hself]

/-! ## Stars of a base of simple roots -/

variable {B : Set L.obj.obj.carrier}

/-- The members of a base are the values of the basis it presents. -/
theorem IsRootBase.basis_apply (hB : IsRootBase L B) (i : B) :
    hB.basis i = (i : L.obj.obj.carrier) :=
  Module.Basis.mk_apply _ _ _

/-- The coordinate of a member of a base at itself is `1`. -/
theorem IsRootBase.repr_basis_self (hB : IsRootBase L B) (i : B) :
    hB.basis.repr (i : L.obj.obj.carrier) i = 1 := by
  rw [← hB.basis_apply i, hB.basis.repr_self, Finsupp.single_eq_same]

/-- The weighted sum along an arm of members of a base has coordinate zero at any member of the
base outside the arm. This is what makes the combination of `arm_length_inequality_of_gram`
nonzero: only the branch node contributes to its coordinate there. -/
theorem IsRootBase.repr_armVector_eq_zero (hB : IsRootBase L B) {x : ℕ → B} {n : ℕ} {c : B}
    (h : ∀ i, i < n → x i ≠ c) :
    hB.basis.repr (L.armVector (fun i => (x i : L.obj.obj.carrier)) n) c = 0 := by
  classical
  rw [armVector, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hne : x i ≠ c := h i (Finset.mem_range.mp hi)
  rw [← hB.basis_apply (x i), map_zsmul, hB.basis.repr_self]
  simp [hne]

/-- A three-armed star inside a base of simple roots: a branch node `c` together with three arms
`x 0, x 1, x 2` of lengths `k 0, k 1, k 2`, indexed from their far ends inwards. The branch node
is orthogonal to every vertex of every arm except the inner end of each, where it pairs to `1`,
and the three arms are pairwise orthogonal. The last condition is that no vertex of an arm is
the branch node, which is what linear independence needs to see. -/
structure IsThreeArmStar (L : FiniteProjectiveLatticeCat ℤ ℤ) (B : Set L.obj.obj.carrier)
    (c : B) (x : Fin 3 → ℕ → B) (k : Fin 3 → ℕ) : Prop where
  /-- Each of the three arms is an arm. -/
  isArm : ∀ t, IsArm L (fun i => (x t i : L.obj.obj.carrier)) (k t)
  /-- The branch node is a root of the single level set `-2`. -/
  pairing_branch_self : L.obj.obj.pairing (c : L.obj.obj.carrier) c = -2
  /-- The branch node is orthogonal to every vertex of an arm but the inner end. -/
  pairing_branch_far : ∀ t i, i + 1 < k t →
    L.obj.obj.pairing (x t i : L.obj.obj.carrier) c = 0
  /-- The branch node pairs to `1` with the inner end of each arm. -/
  pairing_branch_near : ∀ t i, i + 1 = k t →
    L.obj.obj.pairing (x t i : L.obj.obj.carrier) c = 1
  /-- Vertices of two different arms are orthogonal. -/
  pairing_arm : ∀ t u, t ≠ u → ∀ i, i < k t → ∀ j, j < k u →
    L.obj.obj.pairing (x t i : L.obj.obj.carrier) (x u j) = 0
  /-- No vertex of an arm is the branch node. -/
  ne_branch : ∀ t i, i < k t → x t i ≠ c

/-- The weighted sum along the `t`-th arm of a star. -/
def starVector (L : FiniteProjectiveLatticeCat ℤ ℤ) {B : Set L.obj.obj.carrier}
    (x : Fin 3 → ℕ → B) (k : Fin 3 → ℕ) (t : Fin 3) : L.obj.obj.carrier :=
  L.armVector (fun i => (x t i : L.obj.obj.carrier)) (k t)

namespace IsThreeArmStar

variable {c : B} {x : Fin 3 → ℕ → B} {k : Fin 3 → ℕ}

/-- The self-pairing of the weighted sum along an arm of a star. -/
theorem pairing_starVector_self (hstar : IsThreeArmStar L B c x k) (t : Fin 3) :
    L.obj.obj.pairing (L.starVector x k t) (L.starVector x k t)
      = -((k t : ℤ) * ((k t : ℤ) + 1)) :=
  pairing_armVector_self L (fun i => (x t i : L.obj.obj.carrier)) (k t) (hstar.isArm t)

/-- The pairing of the weighted sum along an arm of a star with the branch node. -/
theorem pairing_starVector_branch (hstar : IsThreeArmStar L B c x k) (t : Fin 3) :
    L.obj.obj.pairing (L.starVector x k t) (c : L.obj.obj.carrier) = (k t : ℤ) :=
  pairing_armVector_branch L (x := fun i => (x t i : L.obj.obj.carrier)) (n := k t)
    (y := (c : L.obj.obj.carrier)) (hstar.pairing_branch_far t) (hstar.pairing_branch_near t)

/-- Two different arms of a star are orthogonal. -/
theorem pairing_starVector_ne (hstar : IsThreeArmStar L B c x k) {t u : Fin 3} (htu : t ≠ u) :
    L.obj.obj.pairing (L.starVector x k t) (L.starVector x k u) = 0 := by
  rw [starVector, starVector, armVector, armVector, pairing_sum_left]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [BilinModuleCat.pairing_zsmul_left, pairing_sum_right]
  have : ∑ j ∈ Finset.range (k u),
      L.obj.obj.pairing (x t i : L.obj.obj.carrier) (((j : ℤ) + 1) • (x u j : _)) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [BilinModuleCat.pairing_zsmul_right,
      hstar.pairing_arm t u htu i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj), smul_zero]
  rw [this, smul_zero]

/-- The combination of `arm_length_inequality_of_gram` for a star of a base is nonzero: its
coordinate at the branch node is the product of the three arm lengths. -/
theorem combination_ne_zero (hB : IsRootBase L B) (hstar : IsThreeArmStar L B c x k) :
    (((k 0 : ℤ) + 1) * ((k 1 : ℤ) + 1) * ((k 2 : ℤ) + 1)) • (c : L.obj.obj.carrier)
        + (((k 1 : ℤ) + 1) * ((k 2 : ℤ) + 1)) • L.starVector x k 0
        + (((k 0 : ℤ) + 1) * ((k 2 : ℤ) + 1)) • L.starVector x k 1
        + (((k 0 : ℤ) + 1) * ((k 1 : ℤ) + 1)) • L.starVector x k 2 ≠ 0 := by
  intro hzero
  have hcoord := congrArg (fun v => hB.basis.repr v c) hzero
  simp only [map_add, Finsupp.add_apply, map_zero, Finsupp.zero_apply] at hcoord
  rw [← Int.cast_smul_eq_zsmul ℤ, ← Int.cast_smul_eq_zsmul ℤ, ← Int.cast_smul_eq_zsmul ℤ,
    ← Int.cast_smul_eq_zsmul ℤ] at hcoord
  simp only [map_smul, Finsupp.smul_apply, Int.cast_id, smul_eq_mul,
    hB.repr_basis_self c] at hcoord
  rw [starVector, starVector, starVector,
    hB.repr_armVector_eq_zero (hstar.ne_branch 0),
    hB.repr_armVector_eq_zero (hstar.ne_branch 1),
    hB.repr_armVector_eq_zero (hstar.ne_branch 2)] at hcoord
  simp only [mul_zero, add_zero, mul_one] at hcoord
  have hpos : (0 : ℤ) < ((k 0 : ℤ) + 1) * ((k 1 : ℤ) + 1) * ((k 2 : ℤ) + 1) := by positivity
  exact hpos.ne' hcoord

/-- The arm length bound. Writing `p, q, r` for the lengths of the three arms of a star of a
base of simple roots of an even negative definite lattice, counted with the branch node,
`pqr < qr + pr + pq`, which is the integer form of `1/p + 1/q + 1/r > 1`. -/
theorem arm_length_inequality (hL : IsNegativeDefiniteLattice L) (hB : IsRootBase L B)
    (hstar : IsThreeArmStar L B c x k) :
    ((k 0 : ℤ) + 1) * ((k 1 : ℤ) + 1) * ((k 2 : ℤ) + 1) <
      ((k 1 : ℤ) + 1) * ((k 2 : ℤ) + 1) + ((k 0 : ℤ) + 1) * ((k 2 : ℤ) + 1)
        + ((k 0 : ℤ) + 1) * ((k 1 : ℤ) + 1) := by
  refine arm_length_inequality_of_gram L hL (c := (c : L.obj.obj.carrier))
    (A₀ := L.starVector x k 0) (A₁ := L.starVector x k 1) (A₂ := L.starVector x k 2)
    (by positivity) (by positivity) (by positivity) hstar.pairing_branch_self
    (by rw [hstar.pairing_starVector_self 0]; ring)
    (by rw [hstar.pairing_starVector_self 1]; ring)
    (by rw [hstar.pairing_starVector_self 2]; ring)
    (by rw [hstar.pairing_starVector_branch 0]; ring)
    (by rw [hstar.pairing_starVector_branch 1]; ring)
    (by rw [hstar.pairing_starVector_branch 2]; ring)
    (hstar.pairing_starVector_ne (by decide)) (hstar.pairing_starVector_ne (by decide))
    (hstar.pairing_starVector_ne (by decide)) (hstar.combination_ne_zero hB)

end IsThreeArmStar

/-! ## The ADE triples -/

/-- The integer form of `1 < 1/p + 1/q + 1/r` for positive `p, q, r`. -/
theorem one_lt_sumInv_of_mul_lt (p q r : ℕ+)
    (h : ((p : ℕ) : ℤ) * ((q : ℕ) : ℤ) * ((r : ℕ) : ℤ) <
      ((q : ℕ) : ℤ) * ((r : ℕ) : ℤ) + ((p : ℕ) : ℤ) * ((r : ℕ) : ℤ)
        + ((p : ℕ) : ℤ) * ((q : ℕ) : ℤ)) :
    1 < ADEInequality.sumInv {p, q, r} := by
  rw [ADEInequality.sumInv_pqr]
  have hp : (0 : ℚ) < ((p : ℕ) : ℚ) := by exact_mod_cast p.pos
  have hq : (0 : ℚ) < ((q : ℕ) : ℚ) := by exact_mod_cast q.pos
  have hr : (0 : ℚ) < ((r : ℕ) : ℚ) := by exact_mod_cast r.pos
  have hcast : ((p : ℕ) : ℚ) * ((q : ℕ) : ℚ) * ((r : ℕ) : ℚ) <
      ((q : ℕ) : ℚ) * ((r : ℕ) : ℚ) + ((p : ℕ) : ℚ) * ((r : ℕ) : ℚ)
        + ((p : ℕ) : ℚ) * ((q : ℕ) : ℚ) := by exact_mod_cast h
  have hkey : (((p : ℕ) : ℚ))⁻¹ + (((q : ℕ) : ℚ))⁻¹ + (((r : ℕ) : ℚ))⁻¹ - 1
      = (((q : ℕ) : ℚ) * ((r : ℕ) : ℚ) + ((p : ℕ) : ℚ) * ((r : ℕ) : ℚ)
          + ((p : ℕ) : ℚ) * ((q : ℕ) : ℚ) - ((p : ℕ) : ℚ) * ((q : ℕ) : ℚ) * ((r : ℕ) : ℚ))
        / (((p : ℕ) : ℚ) * ((q : ℕ) : ℚ) * ((r : ℕ) : ℚ)) := by
    field_simp
  have hpos : (0 : ℚ) < (((p : ℕ) : ℚ))⁻¹ + (((q : ℕ) : ℚ))⁻¹ + (((r : ℕ) : ℚ))⁻¹ - 1 := by
    rw [hkey]
    exact div_pos (by linarith) (by positivity)
  have hcoe : ∀ n : ℕ+, ((n : ℚ)) = ((n : ℕ) : ℚ) := fun _ => rfl
  rw [hcoe p, hcoe q, hcoe r]
  linarith

/-- The classification consequence. The three arm lengths of a star of a base of simple roots of
an even negative definite lattice, counted with the branch node, form one of the ADE triples
enumerated by `Mathlib.NumberTheory.ADEInequality`: `(1, q, r)`, `(2, 2, r)`, `(2, 3, 3)`,
`(2, 3, 4)` or `(2, 3, 5)`. -/
theorem IsThreeArmStar.admissible {c : B} {x : Fin 3 → ℕ → B} {k : Fin 3 → ℕ}
    (hL : IsNegativeDefiniteLattice L) (hB : IsRootBase L B)
    (hstar : IsThreeArmStar L B c x k) :
    ADEInequality.Admissible {(k 0).succPNat, (k 1).succPNat, (k 2).succPNat} := by
  refine ADEInequality.admissible_of_one_lt_sumInv (one_lt_sumInv_of_mul_lt _ _ _ ?_)
  have h := hstar.arm_length_inequality hL hB
  simp only [Nat.succPNat_coe]
  push_cast
  linarith

end FiniteProjectiveLatticeCat

end LeanCategories.Lattices.Valued

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib

/-!
# The sign lemma for the Cartan form of `E₁₀`

This file proves the arithmetic core of the Vinberg chamber of `E₁₀(2)` (#23): the statement that an
integral vector on which the quadratic form of the `E₁₀` diagram takes the value `2` — that is, a
vector of square `-4` of `E₁₀(2)` in the simple-root coordinates — has all its coordinates of one
sign. That is exactly the hypothesis a wall set must satisfy for the criterion
`isChamberWithWalls_of_signs` of `WeylChambers.lean`: every negative reflective root must be a
combination of the simple roots whose coefficients all have one sign.

## The data

* `e10Edge`, `e10Adjacency`, `e10Cartan`: the `E₁₀` diagram in the node order `α₀, …, α₈, α₋₁`
  (node `0` the affine node of `E₉ = E₁₀ ∖ {α₋₁}`, nodes `1 … 8` the `E₈` simple roots in the
  order of `e8GramMatrix`, node `9` the hyperbolic extension), its adjacency matrix, and its Cartan
  matrix `C = 2 · 1 - A` with determinant `-1` (`e10Cartan_eq`, `e10Cartan_mul_inverse`,
  `e10Cartan_inverse_mul`).
* `quadC b = b ⬝ᵥ (C b)`, the Cartan form in those coordinates. For `v = Σ bᵢ αᵢ` in the
  doubled lattice `E₁₀(2)` one has `(v, v) = -2 · quadC b` (`VinbergE10Chamber.e10Root_pairing`),
  so a negative root of square `-4` is exactly a vector with `quadC b = 2`.
* `e10NullVector` is the null vector `δ` of the affine subdiagram `E₉`.

## The proof

The sign lemma is proved from a positivity statement for the Cartan form away from the orthant's
interior. For each of the ten nodes `i` there is an explicit sum-of-squares certificate
`cert_i`: if `u i = 0` then `N · quadC u` is a sum of squares with positive integral coefficients
(the pivots of the `LDLᵀ` elimination of the principal submatrix `C[univ \ {i}]`, rooted at the
trivalent node `4`). Hence:

* `quadC_nonneg_of_zero`: `quadC u ≥ 0` whenever `u` vanishes at some node — the form is
  nonnegative on every proper coordinate subspace of the orthant;
* `quadC_eq_zero_of_zero`: if in addition `quadC u = 0` then `u` is a multiple of the null vector
  `δ` (`u = k · δ`; the pivot at node `4` in the `i = 9` certificate is `0`, which is exactly the
  affine degeneracy of `E₉`, and the resolution of the triangular system reproduces `δ`).

Then, for a vector `b` of `quadC`-value `2` that changes sign, the decomposition `b = u - v` into
positive and negative parts gives
`2 = quadC u + quadC v + 2 · Σ_{edges} (u a · v b + v a · u b)`, with all three terms nonnegative
and the first two even; each part therefore is either `0` (a multiple of `δ`) or at least `2`, and
in the degenerate case the edge between the two supports contributes at least `2` more. Either way
`quadC b ≥ 4`, contradicting `quadC b = 2` (`quadC_eq_two_signs`).

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, 3rd ed., Ch. 5, §5.1: the real roots of a
  Kac–Moody algebra with a symmetrizable Cartan matrix are the `W`-translates of the simple roots,
  and `W` preserves the partition of the root lattice into positive and negative roots
  (Prop. 5.1).
* È. B. Vinberg, *The groups of unit elements of certain quadratic forms*, Mat. Sb. 87 (1972), §3.

## LC-09 record

Searched (Mathlib at the pinned head, and the formalization corpus):
`content:PosSemidef submatrix`, `content:Matrix.PosDef.submatrix`, `content:CartanMatrix E8`,
`content:positive semidefinite principal submatrix`, `content:Vinberg chamber Lorentzian root
system`, `content:IsCoxeter`, plus local greps for `IsCoxeter`, `FundamentalDomain`, `chamber`,
`CartanMatrix` over `Mathlib/`.

Hits. Mathlib has `CartanMatrix.E n` (`Mathlib/LinearAlgebra/Matrix/Cartan/Basic.lean`, the
generalized Cartan matrix of type `Eₙ`, so `CartanMatrix.E 10` is the matrix `e10Cartan` up to the
node order) with `E_det`, `E_off_diag_nonpos`, `isSimplyLaced_E`, and the predicate
`Matrix.IsFiniteCartan` with `det_pos` and `transpose`. None of it supplies the statement used here:
`IsFiniteCartan` is defined *by* the existence of a positive-definite symmetrization
(`exists_posDef`), so it cannot certify positive semidefiniteness, and Mathlib has no
positive-semidefiniteness criterion for a diagram of affine or indefinite type and no null-vector
statement. The corpus's nearest neighbours are `Atlas`'s `PositiveDefinite`/`HyperplaneArrangement`
material and TauCeti's `Matrix.IsFiniteCartan.toSymmetrizableDatum`
(`TauCeti/LinearAlgebra/Matrix/Cartan/Symmetrizable.lean`), both of which start from a Cartan matrix
already known to be of finite type. The certificates below are therefore proved directly by
`ring` on the explicit quadratic form; the only Mathlib API used is `Matrix.PosDef.submatrix`
(the model for the statement, not usable without a positive-definite matrix in hand).
-/

@[expose] public section

open Matrix
open scoped BigOperators

namespace LeanCategories.Lattices.Valued

/-! ## The `E₁₀` diagram -/

/-- The nine edges of the `E₁₀` diagram, in the node order `α₀, α₁, …, α₈, α₋₁`: the `E₈` chain,
the affine node `0` attached to `α₈` (node `8`), and the hyperbolic node `9` attached to the affine
node. -/
def e10Edge : Fin 9 → Fin 10 × Fin 10 :=
  ![(0, 8), (0, 9), (1, 3), (2, 4), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8)]

/-- The adjacency matrix of the `E₁₀` diagram, as the sum of the elementary matrices of its edges.
Symmetric by construction; this is the form in which the quadratic form of the diagram is
manipulated. -/
def e10Adjacency : Matrix (Fin 10) (Fin 10) ℤ :=
  ∑ k, (Matrix.single (e10Edge k).1 (e10Edge k).2 1 +
    Matrix.single (e10Edge k).2 (e10Edge k).1 1)

/-- The Cartan matrix of the `E₁₀` diagram: `2` on the diagonal and `-1` on the edges. -/
def e10Cartan : Matrix (Fin 10) (Fin 10) ℤ := ![
  ![ 2,  0,  0,  0,  0,  0,  0,  0, -1, -1],
  ![ 0,  2,  0, -1,  0,  0,  0,  0,  0,  0],
  ![ 0,  0,  2,  0, -1,  0,  0,  0,  0,  0],
  ![ 0, -1,  0,  2, -1,  0,  0,  0,  0,  0],
  ![ 0,  0, -1, -1,  2, -1,  0,  0,  0,  0],
  ![ 0,  0,  0,  0, -1,  2, -1,  0,  0,  0],
  ![ 0,  0,  0,  0,  0, -1,  2, -1,  0,  0],
  ![ 0,  0,  0,  0,  0,  0, -1,  2, -1,  0],
  ![-1,  0,  0,  0,  0,  0,  0, -1,  2,  0],
  ![-1,  0,  0,  0,  0,  0,  0,  0,  0,  2]]

set_option maxHeartbeats 1000000 in
/-- The Cartan matrix is `2 · 1` minus the adjacency matrix. -/
theorem e10Cartan_eq :
    e10Cartan = 2 • (1 : Matrix (Fin 10) (Fin 10) ℤ) - e10Adjacency := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- An integral inverse for the `E₁₀` Cartan matrix. -/
def e10CartanInverse : Matrix (Fin 10) (Fin 10) ℤ := ![
  ![ -2,  -4,  -6,  -8, -12, -10,  -8,  -6,  -4,  -1],
  ![ -4,  -4,  -7,  -9, -14, -12, -10,  -8,  -6,  -2],
  ![ -6,  -7, -10, -14, -21, -18, -15, -12,  -9,  -3],
  ![ -8,  -9, -14, -18, -28, -24, -20, -16, -12,  -4],
  ![-12, -14, -21, -28, -42, -36, -30, -24, -18,  -6],
  ![-10, -12, -18, -24, -36, -30, -25, -20, -15,  -5],
  ![ -8, -10, -15, -20, -30, -25, -20, -16, -12,  -4],
  ![ -6,  -8, -12, -16, -24, -20, -16, -12,  -9,  -3],
  ![ -4,  -6,  -9, -12, -18, -15, -12,  -9,  -6,  -2],
  ![ -1,  -2,  -3,  -4,  -6,  -5,  -4,  -3,  -2,   0]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The displayed integral matrix is a right inverse of the `E₁₀` Cartan matrix. -/
theorem e10Cartan_mul_inverse : e10Cartan * e10CartanInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e10Cartan, e10CartanInverse, Matrix.mul_apply, Fin.sum_univ_succ] <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The displayed integral matrix is a left inverse of the `E₁₀` Cartan matrix. -/
theorem e10Cartan_inverse_mul : e10CartanInverse * e10Cartan = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e10Cartan, e10CartanInverse, Matrix.mul_apply, Fin.sum_univ_succ] <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The `E₁₀` Cartan matrix is symmetric. -/
theorem e10Cartan_isSymm : e10Cartan.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-! ## The quadratic form of the diagram -/

/-- The quadratic form of a `ℤ`-vector in the simple-root coordinates of `E₁₀`:
`b ⬝ᵥ (C b)`. A vector of square `-4` of `E₁₀(2)` has `quadC b = 2`. -/
def quadC (b : Fin 10 → ℤ) : ℤ := b ⬝ᵥ (e10Cartan *ᵥ b)

/-- The Cartesian expansion of the Cartan form: the squares with the doubled edge pairings. -/
theorem quadC_explicit (u : Fin 10 → ℤ) :
    quadC u = 2 * u 0 ^ 2 + 2 * u 1 ^ 2 + 2 * u 2 ^ 2 + 2 * u 3 ^ 2 + 2 * u 4 ^ 2
      + 2 * u 5 ^ 2 + 2 * u 6 ^ 2 + 2 * u 7 ^ 2 + 2 * u 8 ^ 2 + 2 * u 9 ^ 2
      - 2 * (u 0 * u 8) - 2 * (u 0 * u 9) - 2 * (u 1 * u 3) - 2 * (u 2 * u 4)
      - 2 * (u 3 * u 4) - 2 * (u 4 * u 5) - 2 * (u 5 * u 6) - 2 * (u 6 * u 7)
      - 2 * (u 7 * u 8) := by
  simp only [quadC, e10Cartan, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val', Matrix.empty_val',
    Fin.isValue]
  ring_nf
  simp

/-- The Cartan form is even: it is twice an integer. -/
theorem quadC_even (b : Fin 10 → ℤ) : 2 ∣ quadC b := by
  rw [quadC_explicit]
  omega

/-- The null vector `δ` of the affine subdiagram `E₉ = E₁₀ ∖ {α₋₁}`: its coefficients in the simple
roots `α₀, …, α₈`. -/
def e10NullVector : Fin 10 → ℤ := ![1, 2, 3, 4, 6, 5, 4, 3, 2, 0]

/-- The Cartan form of the null vector vanishes: `E₉` is of affine type. -/
theorem quadC_e10NullVector : quadC e10NullVector = 0 := by decide

set_option maxHeartbeats 1000000 in
/-- The Cartan form is homogeneous of degree two on integer multiples. -/
theorem quadC_smul (k : ℤ) (b : Fin 10 → ℤ) : quadC (k • b) = k ^ 2 * quadC b := by
  simp only [quadC_explicit, Pi.smul_apply, smul_eq_mul]
  ring

/-- The Cartan form vanishes on every integer multiple of the null vector. -/
theorem quadC_nullVector (k : ℤ) : quadC (k • e10NullVector) = 0 := by
  rw [quadC_smul, quadC_e10NullVector]
  ring

/-- The null vector is positive away from the extra node. -/
theorem e10NullVector_pos {i : Fin 10} (hi : i ≠ 9) : 0 < e10NullVector i := by
  fin_cases i <;> simp_all [e10NullVector]

/-- The extra node is not in the support of the null vector. -/
theorem e10NullVector_nine : e10NullVector 9 = 0 := by decide

/-- The null vector's first coefficient is `1`. -/
theorem e10NullVector_zero : e10NullVector 0 = 1 := by decide

/-! ## The bilinear expansion along the diagram -/

/-- The Cartan form of a difference, expanded along the edges of the diagram. -/
theorem quadC_sub (u v : Fin 10 → ℤ) :
    quadC (u - v) = quadC u + quadC v
      - 4 * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 + u 4 * v 4
        + u 5 * v 5 + u 6 * v 6 + u 7 * v 7 + u 8 * v 8 + u 9 * v 9)
      + 2 * (u 0 * v 8 + v 0 * u 8 + u 0 * v 9 + v 0 * u 9
        + u 1 * v 3 + v 1 * u 3 + u 2 * v 4 + v 2 * u 4
        + u 3 * v 4 + v 3 * u 4 + u 4 * v 5 + v 4 * u 5
        + u 5 * v 6 + v 5 * u 6 + u 6 * v 7 + v 6 * u 7
        + u 7 * v 8 + v 7 * u 8) := by
  simp only [quadC_explicit, Pi.sub_apply]
  ring


/-! ## The sum-of-squares certificates at the ten nodes -/

set_option maxHeartbeats 1000000 in
/-- Certificate at node `0`: if `u 0 = 0` then `60` times the Cartan form of `E₁₀` is a sum
of squares with positive integral coefficients. -/
theorem e10CertZero (u : Fin 10 → ℤ) (h : u 0 = 0) :
    60 * quadC u =
      30 * (2 * u 1 - u 3) ^ 2 + 30 * (2 * u 2 - u 4) ^ 2
      + 10 * (3 * u 3 - 2 * u 4) ^ 2 + 2 * u 4 ^ 2
      + 3 * (5 * u 5 - 4 * u 4) ^ 2 + 5 * (4 * u 6 - 3 * u 5) ^ 2
      + 10 * (3 * u 7 - 2 * u 6) ^ 2 + 30 * (2 * u 8 - u 7) ^ 2
      + 120 * u 9 ^ 2 := by
  rw [quadC_explicit, h]
  ring

set_option maxHeartbeats 1000000 in
theorem e10NonnegZero (u : Fin 10 → ℤ) (h : u 0 = 0) : 0 ≤ quadC u := by
  have hk := e10CertZero u h
  nlinarith [hk, sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (5 * u 5 - 4 * u 4), sq_nonneg (4 * u 6 - 3 * u 5),
      sq_nonneg (3 * u 7 - 2 * u 6), sq_nonneg (2 * u 8 - u 7),
      sq_nonneg (u 9)]

set_option maxHeartbeats 1000000 in
theorem e10KernZero (u : Fin 10 → ℤ) (h : u 0 = 0) (hq : quadC u = 0) :
    u = u 0 • e10NullVector := by
  have hsum :
      30 * (2 * u 1 - u 3) ^ 2 + 30 * (2 * u 2 - u 4) ^ 2
      + 10 * (3 * u 3 - 2 * u 4) ^ 2 + 2 * u 4 ^ 2
      + 3 * (5 * u 5 - 4 * u 4) ^ 2 + 5 * (4 * u 6 - 3 * u 5) ^ 2
      + 10 * (3 * u 7 - 2 * u 6) ^ 2 + 30 * (2 * u 8 - u 7) ^ 2
      + 120 * u 9 ^ 2 = 0 := by
    have hk := e10CertZero u h
    linarith [hk, hq]
  have h1 : 2 * u 1 - u 3 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (5 * u 5 - 4 * u 4), sq_nonneg (4 * u 6 - 3 * u 5),
      sq_nonneg (3 * u 7 - 2 * u 6), sq_nonneg (2 * u 8 - u 7),
      sq_nonneg (u 9)]
  have h2 : 2 * u 2 - u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (5 * u 5 - 4 * u 4), sq_nonneg (4 * u 6 - 3 * u 5),
      sq_nonneg (3 * u 7 - 2 * u 6), sq_nonneg (2 * u 8 - u 7),
      sq_nonneg (u 9)]
  have h3 : 3 * u 3 - 2 * u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (5 * u 5 - 4 * u 4), sq_nonneg (4 * u 6 - 3 * u 5),
      sq_nonneg (3 * u 7 - 2 * u 6), sq_nonneg (2 * u 8 - u 7),
      sq_nonneg (u 9)]
  have h4 : u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (5 * u 5 - 4 * u 4), sq_nonneg (4 * u 6 - 3 * u 5),
      sq_nonneg (3 * u 7 - 2 * u 6), sq_nonneg (2 * u 8 - u 7),
      sq_nonneg (u 9)]
  have h5 : 5 * u 5 - 4 * u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (5 * u 5 - 4 * u 4), sq_nonneg (4 * u 6 - 3 * u 5),
      sq_nonneg (3 * u 7 - 2 * u 6), sq_nonneg (2 * u 8 - u 7),
      sq_nonneg (u 9)]
  have h6 : 4 * u 6 - 3 * u 5 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (5 * u 5 - 4 * u 4), sq_nonneg (4 * u 6 - 3 * u 5),
      sq_nonneg (3 * u 7 - 2 * u 6), sq_nonneg (2 * u 8 - u 7),
      sq_nonneg (u 9)]
  have h7 : 3 * u 7 - 2 * u 6 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (5 * u 5 - 4 * u 4), sq_nonneg (4 * u 6 - 3 * u 5),
      sq_nonneg (3 * u 7 - 2 * u 6), sq_nonneg (2 * u 8 - u 7),
      sq_nonneg (u 9)]
  have h8 : 2 * u 8 - u 7 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (5 * u 5 - 4 * u 4), sq_nonneg (4 * u 6 - 3 * u 5),
      sq_nonneg (3 * u 7 - 2 * u 6), sq_nonneg (2 * u 8 - u 7),
      sq_nonneg (u 9)]
  have h9 : u 9 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (5 * u 5 - 4 * u 4), sq_nonneg (4 * u 6 - 3 * u 5),
      sq_nonneg (3 * u 7 - 2 * u 6), sq_nonneg (2 * u 8 - u 7),
      sq_nonneg (u 9)]
  funext j
  fin_cases j <;> simp [e10NullVector] <;> linarith [h1, h2, h3, h4, h5, h6, h7, h8, h9]

set_option maxHeartbeats 1000000 in
/-- Certificate at node `1`: if `u 1 = 0` then `420` times the Cartan form of `E₁₀` is a sum
of squares with positive integral coefficients. -/
theorem e10CertOne (u : Fin 10 → ℤ) (h : u 1 = 0) :
    420 * quadC u =
      70 * (3 * u 0 - 2 * u 8) ^ 2 + 210 * (2 * u 2 - u 4) ^ 2
      + 210 * (2 * u 3 - u 4) ^ 2 + 60 * u 4 ^ 2
      + 10 * (7 * u 5 - 6 * u 4) ^ 2 + 14 * (6 * u 6 - 5 * u 5) ^ 2
      + 21 * (5 * u 7 - 4 * u 6) ^ 2 + 35 * (4 * u 8 - 3 * u 7) ^ 2
      + 210 * (2 * u 9 - u 0) ^ 2 := by
  rw [quadC_explicit, h]
  ring

set_option maxHeartbeats 1000000 in
theorem e10NonnegOne (u : Fin 10 → ℤ) (h : u 1 = 0) : 0 ≤ quadC u := by
  have hk := e10CertOne u h
  nlinarith [hk, sq_nonneg (3 * u 0 - 2 * u 8), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (2 * u 3 - u 4), sq_nonneg (u 4),
      sq_nonneg (7 * u 5 - 6 * u 4), sq_nonneg (6 * u 6 - 5 * u 5),
      sq_nonneg (5 * u 7 - 4 * u 6), sq_nonneg (4 * u 8 - 3 * u 7),
      sq_nonneg (2 * u 9 - u 0)]

set_option maxHeartbeats 1000000 in
theorem e10KernOne (u : Fin 10 → ℤ) (h : u 1 = 0) (hq : quadC u = 0) :
    u = u 0 • e10NullVector := by
  have hsum :
      70 * (3 * u 0 - 2 * u 8) ^ 2 + 210 * (2 * u 2 - u 4) ^ 2
      + 210 * (2 * u 3 - u 4) ^ 2 + 60 * u 4 ^ 2
      + 10 * (7 * u 5 - 6 * u 4) ^ 2 + 14 * (6 * u 6 - 5 * u 5) ^ 2
      + 21 * (5 * u 7 - 4 * u 6) ^ 2 + 35 * (4 * u 8 - 3 * u 7) ^ 2
      + 210 * (2 * u 9 - u 0) ^ 2 = 0 := by
    have hk := e10CertOne u h
    linarith [hk, hq]
  have h0 : 3 * u 0 - 2 * u 8 = 0 := by
    nlinarith [hsum, sq_nonneg (3 * u 0 - 2 * u 8), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (2 * u 3 - u 4), sq_nonneg (u 4),
      sq_nonneg (7 * u 5 - 6 * u 4), sq_nonneg (6 * u 6 - 5 * u 5),
      sq_nonneg (5 * u 7 - 4 * u 6), sq_nonneg (4 * u 8 - 3 * u 7),
      sq_nonneg (2 * u 9 - u 0)]
  have h2 : 2 * u 2 - u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (3 * u 0 - 2 * u 8), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (2 * u 3 - u 4), sq_nonneg (u 4),
      sq_nonneg (7 * u 5 - 6 * u 4), sq_nonneg (6 * u 6 - 5 * u 5),
      sq_nonneg (5 * u 7 - 4 * u 6), sq_nonneg (4 * u 8 - 3 * u 7),
      sq_nonneg (2 * u 9 - u 0)]
  have h3 : 2 * u 3 - u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (3 * u 0 - 2 * u 8), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (2 * u 3 - u 4), sq_nonneg (u 4),
      sq_nonneg (7 * u 5 - 6 * u 4), sq_nonneg (6 * u 6 - 5 * u 5),
      sq_nonneg (5 * u 7 - 4 * u 6), sq_nonneg (4 * u 8 - 3 * u 7),
      sq_nonneg (2 * u 9 - u 0)]
  have h4 : u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (3 * u 0 - 2 * u 8), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (2 * u 3 - u 4), sq_nonneg (u 4),
      sq_nonneg (7 * u 5 - 6 * u 4), sq_nonneg (6 * u 6 - 5 * u 5),
      sq_nonneg (5 * u 7 - 4 * u 6), sq_nonneg (4 * u 8 - 3 * u 7),
      sq_nonneg (2 * u 9 - u 0)]
  have h5 : 7 * u 5 - 6 * u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (3 * u 0 - 2 * u 8), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (2 * u 3 - u 4), sq_nonneg (u 4),
      sq_nonneg (7 * u 5 - 6 * u 4), sq_nonneg (6 * u 6 - 5 * u 5),
      sq_nonneg (5 * u 7 - 4 * u 6), sq_nonneg (4 * u 8 - 3 * u 7),
      sq_nonneg (2 * u 9 - u 0)]
  have h6 : 6 * u 6 - 5 * u 5 = 0 := by
    nlinarith [hsum, sq_nonneg (3 * u 0 - 2 * u 8), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (2 * u 3 - u 4), sq_nonneg (u 4),
      sq_nonneg (7 * u 5 - 6 * u 4), sq_nonneg (6 * u 6 - 5 * u 5),
      sq_nonneg (5 * u 7 - 4 * u 6), sq_nonneg (4 * u 8 - 3 * u 7),
      sq_nonneg (2 * u 9 - u 0)]
  have h7 : 5 * u 7 - 4 * u 6 = 0 := by
    nlinarith [hsum, sq_nonneg (3 * u 0 - 2 * u 8), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (2 * u 3 - u 4), sq_nonneg (u 4),
      sq_nonneg (7 * u 5 - 6 * u 4), sq_nonneg (6 * u 6 - 5 * u 5),
      sq_nonneg (5 * u 7 - 4 * u 6), sq_nonneg (4 * u 8 - 3 * u 7),
      sq_nonneg (2 * u 9 - u 0)]
  have h8 : 4 * u 8 - 3 * u 7 = 0 := by
    nlinarith [hsum, sq_nonneg (3 * u 0 - 2 * u 8), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (2 * u 3 - u 4), sq_nonneg (u 4),
      sq_nonneg (7 * u 5 - 6 * u 4), sq_nonneg (6 * u 6 - 5 * u 5),
      sq_nonneg (5 * u 7 - 4 * u 6), sq_nonneg (4 * u 8 - 3 * u 7),
      sq_nonneg (2 * u 9 - u 0)]
  have h9 : 2 * u 9 - u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (3 * u 0 - 2 * u 8), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (2 * u 3 - u 4), sq_nonneg (u 4),
      sq_nonneg (7 * u 5 - 6 * u 4), sq_nonneg (6 * u 6 - 5 * u 5),
      sq_nonneg (5 * u 7 - 4 * u 6), sq_nonneg (4 * u 8 - 3 * u 7),
      sq_nonneg (2 * u 9 - u 0)]
  funext j
  fin_cases j <;> simp [e10NullVector] <;> linarith [h0, h2, h3, h4, h5, h6, h7, h8, h9]

set_option maxHeartbeats 1000000 in
/-- Certificate at node `2`: if `u 2 = 0` then `840` times the Cartan form of `E₁₀` is a sum
of squares with positive integral coefficients. -/
theorem e10CertTwo (u : Fin 10 → ℤ) (h : u 2 = 0) :
    840 * quadC u =
      525 * u 0 ^ 2 + 420 * (2 * u 1 - u 3) ^ 2
      + 140 * (3 * u 3 - 2 * u 4) ^ 2 + 70 * (4 * u 4 - 3 * u 5) ^ 2
      + 42 * (5 * u 5 - 4 * u 6) ^ 2 + 28 * (6 * u 6 - 5 * u 7) ^ 2
      + 20 * (7 * u 7 - 6 * u 8) ^ 2 + 15 * (8 * u 8 - 7 * u 0) ^ 2
      + 420 * (2 * u 9 - u 0) ^ 2 := by
  rw [quadC_explicit, h]
  ring

set_option maxHeartbeats 1000000 in
theorem e10NonnegTwo (u : Fin 10 → ℤ) (h : u 2 = 0) : 0 ≤ quadC u := by
  have hk := e10CertTwo u h
  nlinarith [hk, sq_nonneg (u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (4 * u 4 - 3 * u 5),
      sq_nonneg (5 * u 5 - 4 * u 6), sq_nonneg (6 * u 6 - 5 * u 7),
      sq_nonneg (7 * u 7 - 6 * u 8), sq_nonneg (8 * u 8 - 7 * u 0),
      sq_nonneg (2 * u 9 - u 0)]

set_option maxHeartbeats 1000000 in
theorem e10KernTwo (u : Fin 10 → ℤ) (h : u 2 = 0) (hq : quadC u = 0) :
    u = u 0 • e10NullVector := by
  have hsum :
      525 * u 0 ^ 2 + 420 * (2 * u 1 - u 3) ^ 2
      + 140 * (3 * u 3 - 2 * u 4) ^ 2 + 70 * (4 * u 4 - 3 * u 5) ^ 2
      + 42 * (5 * u 5 - 4 * u 6) ^ 2 + 28 * (6 * u 6 - 5 * u 7) ^ 2
      + 20 * (7 * u 7 - 6 * u 8) ^ 2 + 15 * (8 * u 8 - 7 * u 0) ^ 2
      + 420 * (2 * u 9 - u 0) ^ 2 = 0 := by
    have hk := e10CertTwo u h
    linarith [hk, hq]
  have h0 : u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (4 * u 4 - 3 * u 5),
      sq_nonneg (5 * u 5 - 4 * u 6), sq_nonneg (6 * u 6 - 5 * u 7),
      sq_nonneg (7 * u 7 - 6 * u 8), sq_nonneg (8 * u 8 - 7 * u 0),
      sq_nonneg (2 * u 9 - u 0)]
  have h1 : 2 * u 1 - u 3 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (4 * u 4 - 3 * u 5),
      sq_nonneg (5 * u 5 - 4 * u 6), sq_nonneg (6 * u 6 - 5 * u 7),
      sq_nonneg (7 * u 7 - 6 * u 8), sq_nonneg (8 * u 8 - 7 * u 0),
      sq_nonneg (2 * u 9 - u 0)]
  have h3 : 3 * u 3 - 2 * u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (4 * u 4 - 3 * u 5),
      sq_nonneg (5 * u 5 - 4 * u 6), sq_nonneg (6 * u 6 - 5 * u 7),
      sq_nonneg (7 * u 7 - 6 * u 8), sq_nonneg (8 * u 8 - 7 * u 0),
      sq_nonneg (2 * u 9 - u 0)]
  have h4 : 4 * u 4 - 3 * u 5 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (4 * u 4 - 3 * u 5),
      sq_nonneg (5 * u 5 - 4 * u 6), sq_nonneg (6 * u 6 - 5 * u 7),
      sq_nonneg (7 * u 7 - 6 * u 8), sq_nonneg (8 * u 8 - 7 * u 0),
      sq_nonneg (2 * u 9 - u 0)]
  have h5 : 5 * u 5 - 4 * u 6 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (4 * u 4 - 3 * u 5),
      sq_nonneg (5 * u 5 - 4 * u 6), sq_nonneg (6 * u 6 - 5 * u 7),
      sq_nonneg (7 * u 7 - 6 * u 8), sq_nonneg (8 * u 8 - 7 * u 0),
      sq_nonneg (2 * u 9 - u 0)]
  have h6 : 6 * u 6 - 5 * u 7 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (4 * u 4 - 3 * u 5),
      sq_nonneg (5 * u 5 - 4 * u 6), sq_nonneg (6 * u 6 - 5 * u 7),
      sq_nonneg (7 * u 7 - 6 * u 8), sq_nonneg (8 * u 8 - 7 * u 0),
      sq_nonneg (2 * u 9 - u 0)]
  have h7 : 7 * u 7 - 6 * u 8 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (4 * u 4 - 3 * u 5),
      sq_nonneg (5 * u 5 - 4 * u 6), sq_nonneg (6 * u 6 - 5 * u 7),
      sq_nonneg (7 * u 7 - 6 * u 8), sq_nonneg (8 * u 8 - 7 * u 0),
      sq_nonneg (2 * u 9 - u 0)]
  have h8 : 8 * u 8 - 7 * u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (4 * u 4 - 3 * u 5),
      sq_nonneg (5 * u 5 - 4 * u 6), sq_nonneg (6 * u 6 - 5 * u 7),
      sq_nonneg (7 * u 7 - 6 * u 8), sq_nonneg (8 * u 8 - 7 * u 0),
      sq_nonneg (2 * u 9 - u 0)]
  have h9 : 2 * u 9 - u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (4 * u 4 - 3 * u 5),
      sq_nonneg (5 * u 5 - 4 * u 6), sq_nonneg (6 * u 6 - 5 * u 7),
      sq_nonneg (7 * u 7 - 6 * u 8), sq_nonneg (8 * u 8 - 7 * u 0),
      sq_nonneg (2 * u 9 - u 0)]
  funext j
  fin_cases j <;> simp [e10NullVector] <;> linarith [h0, h1, h3, h4, h5, h6, h7, h8, h9]

set_option maxHeartbeats 1000000 in
/-- Certificate at node `3`: if `u 3 = 0` then `420` times the Cartan form of `E₁₀` is a sum
of squares with positive integral coefficients. -/
theorem e10CertThree (u : Fin 10 → ℤ) (h : u 3 = 0) :
    420 * quadC u =
      270 * u 0 ^ 2 + 210 * (2 * u 2 - u 4) ^ 2
      + 70 * (3 * u 4 - 2 * u 5) ^ 2 + 35 * (4 * u 5 - 3 * u 6) ^ 2
      + 21 * (5 * u 6 - 4 * u 7) ^ 2 + 14 * (6 * u 7 - 5 * u 8) ^ 2
      + 10 * (7 * u 8 - 6 * u 0) ^ 2 + 210 * (2 * u 9 - u 0) ^ 2
      + 840 * u 1 ^ 2 := by
  rw [quadC_explicit, h]
  ring

set_option maxHeartbeats 1000000 in
theorem e10NonnegThree (u : Fin 10 → ℤ) (h : u 3 = 0) : 0 ≤ quadC u := by
  have hk := e10CertThree u h
  nlinarith [hk, sq_nonneg (u 0), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 4 - 2 * u 5), sq_nonneg (4 * u 5 - 3 * u 6),
      sq_nonneg (5 * u 6 - 4 * u 7), sq_nonneg (6 * u 7 - 5 * u 8),
      sq_nonneg (7 * u 8 - 6 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1)]

set_option maxHeartbeats 1000000 in
theorem e10KernThree (u : Fin 10 → ℤ) (h : u 3 = 0) (hq : quadC u = 0) :
    u = u 0 • e10NullVector := by
  have hsum :
      270 * u 0 ^ 2 + 210 * (2 * u 2 - u 4) ^ 2
      + 70 * (3 * u 4 - 2 * u 5) ^ 2 + 35 * (4 * u 5 - 3 * u 6) ^ 2
      + 21 * (5 * u 6 - 4 * u 7) ^ 2 + 14 * (6 * u 7 - 5 * u 8) ^ 2
      + 10 * (7 * u 8 - 6 * u 0) ^ 2 + 210 * (2 * u 9 - u 0) ^ 2
      + 840 * u 1 ^ 2 = 0 := by
    have hk := e10CertThree u h
    linarith [hk, hq]
  have h0 : u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 4 - 2 * u 5), sq_nonneg (4 * u 5 - 3 * u 6),
      sq_nonneg (5 * u 6 - 4 * u 7), sq_nonneg (6 * u 7 - 5 * u 8),
      sq_nonneg (7 * u 8 - 6 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1)]
  have h2 : 2 * u 2 - u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 4 - 2 * u 5), sq_nonneg (4 * u 5 - 3 * u 6),
      sq_nonneg (5 * u 6 - 4 * u 7), sq_nonneg (6 * u 7 - 5 * u 8),
      sq_nonneg (7 * u 8 - 6 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1)]
  have h4 : 3 * u 4 - 2 * u 5 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 4 - 2 * u 5), sq_nonneg (4 * u 5 - 3 * u 6),
      sq_nonneg (5 * u 6 - 4 * u 7), sq_nonneg (6 * u 7 - 5 * u 8),
      sq_nonneg (7 * u 8 - 6 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1)]
  have h5 : 4 * u 5 - 3 * u 6 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 4 - 2 * u 5), sq_nonneg (4 * u 5 - 3 * u 6),
      sq_nonneg (5 * u 6 - 4 * u 7), sq_nonneg (6 * u 7 - 5 * u 8),
      sq_nonneg (7 * u 8 - 6 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1)]
  have h6 : 5 * u 6 - 4 * u 7 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 4 - 2 * u 5), sq_nonneg (4 * u 5 - 3 * u 6),
      sq_nonneg (5 * u 6 - 4 * u 7), sq_nonneg (6 * u 7 - 5 * u 8),
      sq_nonneg (7 * u 8 - 6 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1)]
  have h7 : 6 * u 7 - 5 * u 8 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 4 - 2 * u 5), sq_nonneg (4 * u 5 - 3 * u 6),
      sq_nonneg (5 * u 6 - 4 * u 7), sq_nonneg (6 * u 7 - 5 * u 8),
      sq_nonneg (7 * u 8 - 6 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1)]
  have h8 : 7 * u 8 - 6 * u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 4 - 2 * u 5), sq_nonneg (4 * u 5 - 3 * u 6),
      sq_nonneg (5 * u 6 - 4 * u 7), sq_nonneg (6 * u 7 - 5 * u 8),
      sq_nonneg (7 * u 8 - 6 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1)]
  have h9 : 2 * u 9 - u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 4 - 2 * u 5), sq_nonneg (4 * u 5 - 3 * u 6),
      sq_nonneg (5 * u 6 - 4 * u 7), sq_nonneg (6 * u 7 - 5 * u 8),
      sq_nonneg (7 * u 8 - 6 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1)]
  have h1 : u 1 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 4 - 2 * u 5), sq_nonneg (4 * u 5 - 3 * u 6),
      sq_nonneg (5 * u 6 - 4 * u 7), sq_nonneg (6 * u 7 - 5 * u 8),
      sq_nonneg (7 * u 8 - 6 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1)]
  funext j
  fin_cases j <;> simp [e10NullVector] <;> linarith [h0, h2, h4, h5, h6, h7, h8, h9, h1]

set_option maxHeartbeats 1000000 in
/-- Certificate at node `4`: if `u 4 = 0` then `60` times the Cartan form of `E₁₀` is a sum
of squares with positive integral coefficients. -/
theorem e10CertFour (u : Fin 10 → ℤ) (h : u 4 = 0) :
    60 * quadC u =
      42 * u 0 ^ 2 + 30 * (2 * u 5 - u 6) ^ 2
      + 10 * (3 * u 6 - 2 * u 7) ^ 2 + 5 * (4 * u 7 - 3 * u 8) ^ 2
      + 3 * (5 * u 8 - 4 * u 0) ^ 2 + 30 * (2 * u 9 - u 0) ^ 2
      + 90 * u 1 ^ 2 + 30 * (2 * u 3 - u 1) ^ 2 + 120 * u 2 ^ 2 := by
  rw [quadC_explicit, h]
  ring

set_option maxHeartbeats 1000000 in
theorem e10NonnegFour (u : Fin 10 → ℤ) (h : u 4 = 0) : 0 ≤ quadC u := by
  have hk := e10CertFour u h
  nlinarith [hk, sq_nonneg (u 0), sq_nonneg (2 * u 5 - u 6),
      sq_nonneg (3 * u 6 - 2 * u 7), sq_nonneg (4 * u 7 - 3 * u 8),
      sq_nonneg (5 * u 8 - 4 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1), sq_nonneg (2 * u 3 - u 1), sq_nonneg (u 2)]

set_option maxHeartbeats 1000000 in
theorem e10KernFour (u : Fin 10 → ℤ) (h : u 4 = 0) (hq : quadC u = 0) :
    u = u 0 • e10NullVector := by
  have hsum :
      42 * u 0 ^ 2 + 30 * (2 * u 5 - u 6) ^ 2
      + 10 * (3 * u 6 - 2 * u 7) ^ 2 + 5 * (4 * u 7 - 3 * u 8) ^ 2
      + 3 * (5 * u 8 - 4 * u 0) ^ 2 + 30 * (2 * u 9 - u 0) ^ 2
      + 90 * u 1 ^ 2 + 30 * (2 * u 3 - u 1) ^ 2 + 120 * u 2 ^ 2 = 0 := by
    have hk := e10CertFour u h
    linarith [hk, hq]
  have h0 : u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 5 - u 6),
      sq_nonneg (3 * u 6 - 2 * u 7), sq_nonneg (4 * u 7 - 3 * u 8),
      sq_nonneg (5 * u 8 - 4 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1), sq_nonneg (2 * u 3 - u 1), sq_nonneg (u 2)]
  have h5 : 2 * u 5 - u 6 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 5 - u 6),
      sq_nonneg (3 * u 6 - 2 * u 7), sq_nonneg (4 * u 7 - 3 * u 8),
      sq_nonneg (5 * u 8 - 4 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1), sq_nonneg (2 * u 3 - u 1), sq_nonneg (u 2)]
  have h6 : 3 * u 6 - 2 * u 7 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 5 - u 6),
      sq_nonneg (3 * u 6 - 2 * u 7), sq_nonneg (4 * u 7 - 3 * u 8),
      sq_nonneg (5 * u 8 - 4 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1), sq_nonneg (2 * u 3 - u 1), sq_nonneg (u 2)]
  have h7 : 4 * u 7 - 3 * u 8 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 5 - u 6),
      sq_nonneg (3 * u 6 - 2 * u 7), sq_nonneg (4 * u 7 - 3 * u 8),
      sq_nonneg (5 * u 8 - 4 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1), sq_nonneg (2 * u 3 - u 1), sq_nonneg (u 2)]
  have h8 : 5 * u 8 - 4 * u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 5 - u 6),
      sq_nonneg (3 * u 6 - 2 * u 7), sq_nonneg (4 * u 7 - 3 * u 8),
      sq_nonneg (5 * u 8 - 4 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1), sq_nonneg (2 * u 3 - u 1), sq_nonneg (u 2)]
  have h9 : 2 * u 9 - u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 5 - u 6),
      sq_nonneg (3 * u 6 - 2 * u 7), sq_nonneg (4 * u 7 - 3 * u 8),
      sq_nonneg (5 * u 8 - 4 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1), sq_nonneg (2 * u 3 - u 1), sq_nonneg (u 2)]
  have h1 : u 1 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 5 - u 6),
      sq_nonneg (3 * u 6 - 2 * u 7), sq_nonneg (4 * u 7 - 3 * u 8),
      sq_nonneg (5 * u 8 - 4 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1), sq_nonneg (2 * u 3 - u 1), sq_nonneg (u 2)]
  have h3 : 2 * u 3 - u 1 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 5 - u 6),
      sq_nonneg (3 * u 6 - 2 * u 7), sq_nonneg (4 * u 7 - 3 * u 8),
      sq_nonneg (5 * u 8 - 4 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1), sq_nonneg (2 * u 3 - u 1), sq_nonneg (u 2)]
  have h2 : u 2 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 5 - u 6),
      sq_nonneg (3 * u 6 - 2 * u 7), sq_nonneg (4 * u 7 - 3 * u 8),
      sq_nonneg (5 * u 8 - 4 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (u 1), sq_nonneg (2 * u 3 - u 1), sq_nonneg (u 2)]
  funext j
  fin_cases j <;> simp [e10NullVector] <;> linarith [h0, h5, h6, h7, h8, h9, h1, h3, h2]

set_option maxHeartbeats 1000000 in
/-- Certificate at node `5`: if `u 5 = 0` then `12` times the Cartan form of `E₁₀` is a sum
of squares with positive integral coefficients. -/
theorem e10CertFive (u : Fin 10 → ℤ) (h : u 5 = 0) :
    12 * quadC u =
      9 * u 0 ^ 2 + 6 * (2 * u 6 - u 7) ^ 2
      + 2 * (3 * u 7 - 2 * u 8) ^ 2 + 1 * (4 * u 8 - 3 * u 0) ^ 2
      + 6 * (2 * u 9 - u 0) ^ 2 + 6 * (2 * u 1 - u 3) ^ 2
      + 6 * (2 * u 2 - u 4) ^ 2 + 10 * u 3 ^ 2
      + 2 * (3 * u 4 - 2 * u 3) ^ 2 := by
  rw [quadC_explicit, h]
  ring

set_option maxHeartbeats 1000000 in
theorem e10NonnegFive (u : Fin 10 → ℤ) (h : u 5 = 0) : 0 ≤ quadC u := by
  have hk := e10CertFive u h
  nlinarith [hk, sq_nonneg (u 0), sq_nonneg (2 * u 6 - u 7),
      sq_nonneg (3 * u 7 - 2 * u 8), sq_nonneg (4 * u 8 - 3 * u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (u 3),
      sq_nonneg (3 * u 4 - 2 * u 3)]

set_option maxHeartbeats 1000000 in
theorem e10KernFive (u : Fin 10 → ℤ) (h : u 5 = 0) (hq : quadC u = 0) :
    u = u 0 • e10NullVector := by
  have hsum :
      9 * u 0 ^ 2 + 6 * (2 * u 6 - u 7) ^ 2
      + 2 * (3 * u 7 - 2 * u 8) ^ 2 + 1 * (4 * u 8 - 3 * u 0) ^ 2
      + 6 * (2 * u 9 - u 0) ^ 2 + 6 * (2 * u 1 - u 3) ^ 2
      + 6 * (2 * u 2 - u 4) ^ 2 + 10 * u 3 ^ 2
      + 2 * (3 * u 4 - 2 * u 3) ^ 2 = 0 := by
    have hk := e10CertFive u h
    linarith [hk, hq]
  have h0 : u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 6 - u 7),
      sq_nonneg (3 * u 7 - 2 * u 8), sq_nonneg (4 * u 8 - 3 * u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (u 3),
      sq_nonneg (3 * u 4 - 2 * u 3)]
  have h6 : 2 * u 6 - u 7 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 6 - u 7),
      sq_nonneg (3 * u 7 - 2 * u 8), sq_nonneg (4 * u 8 - 3 * u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (u 3),
      sq_nonneg (3 * u 4 - 2 * u 3)]
  have h7 : 3 * u 7 - 2 * u 8 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 6 - u 7),
      sq_nonneg (3 * u 7 - 2 * u 8), sq_nonneg (4 * u 8 - 3 * u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (u 3),
      sq_nonneg (3 * u 4 - 2 * u 3)]
  have h8 : 4 * u 8 - 3 * u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 6 - u 7),
      sq_nonneg (3 * u 7 - 2 * u 8), sq_nonneg (4 * u 8 - 3 * u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (u 3),
      sq_nonneg (3 * u 4 - 2 * u 3)]
  have h9 : 2 * u 9 - u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 6 - u 7),
      sq_nonneg (3 * u 7 - 2 * u 8), sq_nonneg (4 * u 8 - 3 * u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (u 3),
      sq_nonneg (3 * u 4 - 2 * u 3)]
  have h1 : 2 * u 1 - u 3 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 6 - u 7),
      sq_nonneg (3 * u 7 - 2 * u 8), sq_nonneg (4 * u 8 - 3 * u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (u 3),
      sq_nonneg (3 * u 4 - 2 * u 3)]
  have h2 : 2 * u 2 - u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 6 - u 7),
      sq_nonneg (3 * u 7 - 2 * u 8), sq_nonneg (4 * u 8 - 3 * u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (u 3),
      sq_nonneg (3 * u 4 - 2 * u 3)]
  have h3 : u 3 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 6 - u 7),
      sq_nonneg (3 * u 7 - 2 * u 8), sq_nonneg (4 * u 8 - 3 * u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (u 3),
      sq_nonneg (3 * u 4 - 2 * u 3)]
  have h4 : 3 * u 4 - 2 * u 3 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 6 - u 7),
      sq_nonneg (3 * u 7 - 2 * u 8), sq_nonneg (4 * u 8 - 3 * u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (u 3),
      sq_nonneg (3 * u 4 - 2 * u 3)]
  funext j
  fin_cases j <;> simp [e10NullVector] <;> linarith [h0, h6, h7, h8, h9, h1, h2, h3, h4]

set_option maxHeartbeats 1000000 in
/-- Certificate at node `6`: if `u 6 = 0` then `6` times the Cartan form of `E₁₀` is a sum
of squares with positive integral coefficients. -/
theorem e10CertSix (u : Fin 10 → ℤ) (h : u 6 = 0) :
    6 * quadC u =
      5 * u 0 ^ 2 + 3 * (2 * u 7 - u 8) ^ 2
      + 1 * (3 * u 8 - 2 * u 0) ^ 2 + 3 * (2 * u 9 - u 0) ^ 2
      + 3 * (2 * u 1 - u 3) ^ 2 + 3 * (2 * u 2 - u 4) ^ 2
      + 1 * (3 * u 3 - 2 * u 4) ^ 2 + 2 * u 4 ^ 2
      + 3 * (2 * u 5 - u 4) ^ 2 := by
  rw [quadC_explicit, h]
  ring

set_option maxHeartbeats 1000000 in
theorem e10NonnegSix (u : Fin 10 → ℤ) (h : u 6 = 0) : 0 ≤ quadC u := by
  have hk := e10CertSix u h
  nlinarith [hk, sq_nonneg (u 0), sq_nonneg (2 * u 7 - u 8),
      sq_nonneg (3 * u 8 - 2 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (2 * u 5 - u 4)]

set_option maxHeartbeats 1000000 in
theorem e10KernSix (u : Fin 10 → ℤ) (h : u 6 = 0) (hq : quadC u = 0) :
    u = u 0 • e10NullVector := by
  have hsum :
      5 * u 0 ^ 2 + 3 * (2 * u 7 - u 8) ^ 2
      + 1 * (3 * u 8 - 2 * u 0) ^ 2 + 3 * (2 * u 9 - u 0) ^ 2
      + 3 * (2 * u 1 - u 3) ^ 2 + 3 * (2 * u 2 - u 4) ^ 2
      + 1 * (3 * u 3 - 2 * u 4) ^ 2 + 2 * u 4 ^ 2
      + 3 * (2 * u 5 - u 4) ^ 2 = 0 := by
    have hk := e10CertSix u h
    linarith [hk, hq]
  have h0 : u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 7 - u 8),
      sq_nonneg (3 * u 8 - 2 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (2 * u 5 - u 4)]
  have h7 : 2 * u 7 - u 8 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 7 - u 8),
      sq_nonneg (3 * u 8 - 2 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (2 * u 5 - u 4)]
  have h8 : 3 * u 8 - 2 * u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 7 - u 8),
      sq_nonneg (3 * u 8 - 2 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (2 * u 5 - u 4)]
  have h9 : 2 * u 9 - u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 7 - u 8),
      sq_nonneg (3 * u 8 - 2 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (2 * u 5 - u 4)]
  have h1 : 2 * u 1 - u 3 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 7 - u 8),
      sq_nonneg (3 * u 8 - 2 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (2 * u 5 - u 4)]
  have h2 : 2 * u 2 - u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 7 - u 8),
      sq_nonneg (3 * u 8 - 2 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (2 * u 5 - u 4)]
  have h3 : 3 * u 3 - 2 * u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 7 - u 8),
      sq_nonneg (3 * u 8 - 2 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (2 * u 5 - u 4)]
  have h4 : u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 7 - u 8),
      sq_nonneg (3 * u 8 - 2 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (2 * u 5 - u 4)]
  have h5 : 2 * u 5 - u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 7 - u 8),
      sq_nonneg (3 * u 8 - 2 * u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (2 * u 5 - u 4)]
  funext j
  fin_cases j <;> simp [e10NullVector] <;> linarith [h0, h7, h8, h9, h1, h2, h3, h4, h5]

set_option maxHeartbeats 1000000 in
/-- Certificate at node `7`: if `u 7 = 0` then `6` times the Cartan form of `E₁₀` is a sum
of squares with positive integral coefficients. -/
theorem e10CertSeven (u : Fin 10 → ℤ) (h : u 7 = 0) :
    6 * quadC u =
      6 * u 0 ^ 2 + 3 * (2 * u 8 - u 0) ^ 2
      + 3 * (2 * u 9 - u 0) ^ 2 + 3 * (2 * u 1 - u 3) ^ 2
      + 3 * (2 * u 2 - u 4) ^ 2 + 1 * (3 * u 3 - 2 * u 4) ^ 2
      + 1 * u 4 ^ 2 + 1 * (3 * u 5 - 2 * u 4) ^ 2
      + 3 * (2 * u 6 - u 5) ^ 2 := by
  rw [quadC_explicit, h]
  ring

set_option maxHeartbeats 1000000 in
theorem e10NonnegSeven (u : Fin 10 → ℤ) (h : u 7 = 0) : 0 ≤ quadC u := by
  have hk := e10CertSeven u h
  nlinarith [hk, sq_nonneg (u 0), sq_nonneg (2 * u 8 - u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (u 4), sq_nonneg (3 * u 5 - 2 * u 4),
      sq_nonneg (2 * u 6 - u 5)]

set_option maxHeartbeats 1000000 in
theorem e10KernSeven (u : Fin 10 → ℤ) (h : u 7 = 0) (hq : quadC u = 0) :
    u = u 0 • e10NullVector := by
  have hsum :
      6 * u 0 ^ 2 + 3 * (2 * u 8 - u 0) ^ 2
      + 3 * (2 * u 9 - u 0) ^ 2 + 3 * (2 * u 1 - u 3) ^ 2
      + 3 * (2 * u 2 - u 4) ^ 2 + 1 * (3 * u 3 - 2 * u 4) ^ 2
      + 1 * u 4 ^ 2 + 1 * (3 * u 5 - 2 * u 4) ^ 2
      + 3 * (2 * u 6 - u 5) ^ 2 = 0 := by
    have hk := e10CertSeven u h
    linarith [hk, hq]
  have h0 : u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 8 - u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (u 4), sq_nonneg (3 * u 5 - 2 * u 4),
      sq_nonneg (2 * u 6 - u 5)]
  have h8 : 2 * u 8 - u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 8 - u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (u 4), sq_nonneg (3 * u 5 - 2 * u 4),
      sq_nonneg (2 * u 6 - u 5)]
  have h9 : 2 * u 9 - u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 8 - u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (u 4), sq_nonneg (3 * u 5 - 2 * u 4),
      sq_nonneg (2 * u 6 - u 5)]
  have h1 : 2 * u 1 - u 3 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 8 - u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (u 4), sq_nonneg (3 * u 5 - 2 * u 4),
      sq_nonneg (2 * u 6 - u 5)]
  have h2 : 2 * u 2 - u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 8 - u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (u 4), sq_nonneg (3 * u 5 - 2 * u 4),
      sq_nonneg (2 * u 6 - u 5)]
  have h3 : 3 * u 3 - 2 * u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 8 - u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (u 4), sq_nonneg (3 * u 5 - 2 * u 4),
      sq_nonneg (2 * u 6 - u 5)]
  have h4 : u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 8 - u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (u 4), sq_nonneg (3 * u 5 - 2 * u 4),
      sq_nonneg (2 * u 6 - u 5)]
  have h5 : 3 * u 5 - 2 * u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 8 - u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (u 4), sq_nonneg (3 * u 5 - 2 * u 4),
      sq_nonneg (2 * u 6 - u 5)]
  have h6 : 2 * u 6 - u 5 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 8 - u 0),
      sq_nonneg (2 * u 9 - u 0), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (u 4), sq_nonneg (3 * u 5 - 2 * u 4),
      sq_nonneg (2 * u 6 - u 5)]
  funext j
  fin_cases j <;> simp [e10NullVector] <;> linarith [h0, h8, h9, h1, h2, h3, h4, h5, h6]

set_option maxHeartbeats 1000000 in
/-- Certificate at node `8`: if `u 8 = 0` then `12` times the Cartan form of `E₁₀` is a sum
of squares with positive integral coefficients. -/
theorem e10CertEight (u : Fin 10 → ℤ) (h : u 8 = 0) :
    12 * quadC u =
      18 * u 0 ^ 2 + 6 * (2 * u 9 - u 0) ^ 2
      + 6 * (2 * u 1 - u 3) ^ 2 + 6 * (2 * u 2 - u 4) ^ 2
      + 2 * (3 * u 3 - 2 * u 4) ^ 2 + 1 * u 4 ^ 2
      + 1 * (4 * u 5 - 3 * u 4) ^ 2 + 2 * (3 * u 6 - 2 * u 5) ^ 2
      + 6 * (2 * u 7 - u 6) ^ 2 := by
  rw [quadC_explicit, h]
  ring

set_option maxHeartbeats 1000000 in
theorem e10NonnegEight (u : Fin 10 → ℤ) (h : u 8 = 0) : 0 ≤ quadC u := by
  have hk := e10CertEight u h
  nlinarith [hk, sq_nonneg (u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (4 * u 5 - 3 * u 4), sq_nonneg (3 * u 6 - 2 * u 5),
      sq_nonneg (2 * u 7 - u 6)]

set_option maxHeartbeats 1000000 in
theorem e10KernEight (u : Fin 10 → ℤ) (h : u 8 = 0) (hq : quadC u = 0) :
    u = u 0 • e10NullVector := by
  have hsum :
      18 * u 0 ^ 2 + 6 * (2 * u 9 - u 0) ^ 2
      + 6 * (2 * u 1 - u 3) ^ 2 + 6 * (2 * u 2 - u 4) ^ 2
      + 2 * (3 * u 3 - 2 * u 4) ^ 2 + 1 * u 4 ^ 2
      + 1 * (4 * u 5 - 3 * u 4) ^ 2 + 2 * (3 * u 6 - 2 * u 5) ^ 2
      + 6 * (2 * u 7 - u 6) ^ 2 = 0 := by
    have hk := e10CertEight u h
    linarith [hk, hq]
  have h0 : u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (4 * u 5 - 3 * u 4), sq_nonneg (3 * u 6 - 2 * u 5),
      sq_nonneg (2 * u 7 - u 6)]
  have h9 : 2 * u 9 - u 0 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (4 * u 5 - 3 * u 4), sq_nonneg (3 * u 6 - 2 * u 5),
      sq_nonneg (2 * u 7 - u 6)]
  have h1 : 2 * u 1 - u 3 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (4 * u 5 - 3 * u 4), sq_nonneg (3 * u 6 - 2 * u 5),
      sq_nonneg (2 * u 7 - u 6)]
  have h2 : 2 * u 2 - u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (4 * u 5 - 3 * u 4), sq_nonneg (3 * u 6 - 2 * u 5),
      sq_nonneg (2 * u 7 - u 6)]
  have h3 : 3 * u 3 - 2 * u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (4 * u 5 - 3 * u 4), sq_nonneg (3 * u 6 - 2 * u 5),
      sq_nonneg (2 * u 7 - u 6)]
  have h4 : u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (4 * u 5 - 3 * u 4), sq_nonneg (3 * u 6 - 2 * u 5),
      sq_nonneg (2 * u 7 - u 6)]
  have h5 : 4 * u 5 - 3 * u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (4 * u 5 - 3 * u 4), sq_nonneg (3 * u 6 - 2 * u 5),
      sq_nonneg (2 * u 7 - u 6)]
  have h6 : 3 * u 6 - 2 * u 5 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (4 * u 5 - 3 * u 4), sq_nonneg (3 * u 6 - 2 * u 5),
      sq_nonneg (2 * u 7 - u 6)]
  have h7 : 2 * u 7 - u 6 = 0 := by
    nlinarith [hsum, sq_nonneg (u 0), sq_nonneg (2 * u 9 - u 0),
      sq_nonneg (2 * u 1 - u 3), sq_nonneg (2 * u 2 - u 4),
      sq_nonneg (3 * u 3 - 2 * u 4), sq_nonneg (u 4),
      sq_nonneg (4 * u 5 - 3 * u 4), sq_nonneg (3 * u 6 - 2 * u 5),
      sq_nonneg (2 * u 7 - u 6)]
  funext j
  fin_cases j <;> simp [e10NullVector] <;> linarith [h0, h9, h1, h2, h3, h4, h5, h6, h7]

set_option maxHeartbeats 1000000 in
/-- Certificate at node `9`: if `u 9 = 0` then `60` times the Cartan form of `E₁₀` is a sum
of squares with positive integral coefficients. -/
theorem e10CertNine (u : Fin 10 → ℤ) (h : u 9 = 0) :
    60 * quadC u =
      30 * (2 * u 0 - u 8) ^ 2 + 30 * (2 * u 1 - u 3) ^ 2
      + 30 * (2 * u 2 - u 4) ^ 2 + 10 * (3 * u 3 - 2 * u 4) ^ 2
      + 2 * (6 * u 5 - 5 * u 4) ^ 2 + 3 * (5 * u 6 - 4 * u 5) ^ 2
      + 5 * (4 * u 7 - 3 * u 6) ^ 2 + 10 * (3 * u 8 - 2 * u 7) ^ 2 := by
  rw [quadC_explicit, h]
  ring

set_option maxHeartbeats 1000000 in
theorem e10NonnegNine (u : Fin 10 → ℤ) (h : u 9 = 0) : 0 ≤ quadC u := by
  have hk := e10CertNine u h
  nlinarith [hk, sq_nonneg (2 * u 0 - u 8), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (6 * u 5 - 5 * u 4), sq_nonneg (5 * u 6 - 4 * u 5),
      sq_nonneg (4 * u 7 - 3 * u 6), sq_nonneg (3 * u 8 - 2 * u 7)]

set_option maxHeartbeats 1000000 in
theorem e10KernNine (u : Fin 10 → ℤ) (h : u 9 = 0) (hq : quadC u = 0) :
    u = u 0 • e10NullVector := by
  have hsum :
      30 * (2 * u 0 - u 8) ^ 2 + 30 * (2 * u 1 - u 3) ^ 2
      + 30 * (2 * u 2 - u 4) ^ 2 + 10 * (3 * u 3 - 2 * u 4) ^ 2
      + 2 * (6 * u 5 - 5 * u 4) ^ 2 + 3 * (5 * u 6 - 4 * u 5) ^ 2
      + 5 * (4 * u 7 - 3 * u 6) ^ 2 + 10 * (3 * u 8 - 2 * u 7) ^ 2 = 0 := by
    have hk := e10CertNine u h
    linarith [hk, hq]
  have h0 : 2 * u 0 - u 8 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 0 - u 8), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (6 * u 5 - 5 * u 4), sq_nonneg (5 * u 6 - 4 * u 5),
      sq_nonneg (4 * u 7 - 3 * u 6), sq_nonneg (3 * u 8 - 2 * u 7)]
  have h1 : 2 * u 1 - u 3 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 0 - u 8), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (6 * u 5 - 5 * u 4), sq_nonneg (5 * u 6 - 4 * u 5),
      sq_nonneg (4 * u 7 - 3 * u 6), sq_nonneg (3 * u 8 - 2 * u 7)]
  have h2 : 2 * u 2 - u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 0 - u 8), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (6 * u 5 - 5 * u 4), sq_nonneg (5 * u 6 - 4 * u 5),
      sq_nonneg (4 * u 7 - 3 * u 6), sq_nonneg (3 * u 8 - 2 * u 7)]
  have h3 : 3 * u 3 - 2 * u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 0 - u 8), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (6 * u 5 - 5 * u 4), sq_nonneg (5 * u 6 - 4 * u 5),
      sq_nonneg (4 * u 7 - 3 * u 6), sq_nonneg (3 * u 8 - 2 * u 7)]
  have h5 : 6 * u 5 - 5 * u 4 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 0 - u 8), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (6 * u 5 - 5 * u 4), sq_nonneg (5 * u 6 - 4 * u 5),
      sq_nonneg (4 * u 7 - 3 * u 6), sq_nonneg (3 * u 8 - 2 * u 7)]
  have h6 : 5 * u 6 - 4 * u 5 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 0 - u 8), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (6 * u 5 - 5 * u 4), sq_nonneg (5 * u 6 - 4 * u 5),
      sq_nonneg (4 * u 7 - 3 * u 6), sq_nonneg (3 * u 8 - 2 * u 7)]
  have h7 : 4 * u 7 - 3 * u 6 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 0 - u 8), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (6 * u 5 - 5 * u 4), sq_nonneg (5 * u 6 - 4 * u 5),
      sq_nonneg (4 * u 7 - 3 * u 6), sq_nonneg (3 * u 8 - 2 * u 7)]
  have h8 : 3 * u 8 - 2 * u 7 = 0 := by
    nlinarith [hsum, sq_nonneg (2 * u 0 - u 8), sq_nonneg (2 * u 1 - u 3),
      sq_nonneg (2 * u 2 - u 4), sq_nonneg (3 * u 3 - 2 * u 4),
      sq_nonneg (6 * u 5 - 5 * u 4), sq_nonneg (5 * u 6 - 4 * u 5),
      sq_nonneg (4 * u 7 - 3 * u 6), sq_nonneg (3 * u 8 - 2 * u 7)]
  funext j
  fin_cases j <;> simp [e10NullVector] <;> linarith [h0, h1, h2, h3, h5, h6, h7, h8]

/-! ## The sign lemma -/

set_option maxHeartbeats 1000000 in
/-- **Nonnegativity away from a coordinate hyperplane**: if an integral vector vanishes at some node
of the `E₁₀` diagram then the Cartan form on it is nonnegative. -/
theorem quadC_nonneg_of_zero (u : Fin 10 → ℤ) (i : Fin 10) (h : u i = 0) : 0 ≤ quadC u := by
  fin_cases i
  · exact e10NonnegZero u h
  · exact e10NonnegOne u h
  · exact e10NonnegTwo u h
  · exact e10NonnegThree u h
  · exact e10NonnegFour u h
  · exact e10NonnegFive u h
  · exact e10NonnegSix u h
  · exact e10NonnegSeven u h
  · exact e10NonnegEight u h
  · exact e10NonnegNine u h

set_option maxHeartbeats 1000000 in
/-- **The kernel away from a coordinate hyperplane**: an integral vector vanishing at some node on
which the Cartan form vanishes is a multiple of the null vector `δ` of the affine subdiagram `E₉`. -/
theorem quadC_eq_zero_of_zero (u : Fin 10 → ℤ) (i : Fin 10) (h : u i = 0) (hq : quadC u = 0) :
    ∃ k : ℤ, u = k • e10NullVector := by
  fin_cases i
  · exact ⟨u 0, e10KernZero u h hq⟩
  · exact ⟨u 0, e10KernOne u h hq⟩
  · exact ⟨u 0, e10KernTwo u h hq⟩
  · exact ⟨u 0, e10KernThree u h hq⟩
  · exact ⟨u 0, e10KernFour u h hq⟩
  · exact ⟨u 0, e10KernFive u h hq⟩
  · exact ⟨u 0, e10KernSix u h hq⟩
  · exact ⟨u 0, e10KernSeven u h hq⟩
  · exact ⟨u 0, e10KernEight u h hq⟩
  · exact ⟨u 0, e10KernNine u h hq⟩

set_option maxHeartbeats 2000000 in
/-- **The sign lemma of the `E₁₀` diagram.** An integral vector on which the Cartan form takes the
value `2` — a vector of square `-4` of `E₁₀(2)` in the simple-root coordinates — has all its
coordinates of one sign. Equivalently: every negative reflective root of `E₁₀(2)` is a nonnegative
or a nonpositive integral combination of the ten simple roots (Kac, *Infinite-dimensional Lie
algebras*, Prop. 5.1 and §5.1: the real roots are the `W`-translates of the simple roots, and `W`
preserves the partition of the root lattice into positive and negative roots). -/
theorem quadC_eq_two_signs (b : Fin 10 → ℤ) (hb : quadC b = 2) :
    (∀ i, 0 ≤ b i) ∨ (∀ i, b i ≤ 0) := by
  by_contra hcon
  rw [not_or, not_forall, not_forall] at hcon
  push Not at hcon
  obtain ⟨⟨ineg, hneg⟩, ⟨ipos, hpos⟩⟩ := hcon
  set u : Fin 10 → ℤ := fun i => max (b i) 0 with hu
  set v : Fin 10 → ℤ := fun i => max (-(b i)) 0 with hv
  have hb_eq : b = u - v := by
    funext i
    simp only [hu, hv, Pi.sub_apply]
    omega
  have hu_nn : ∀ i, 0 ≤ u i := fun i => le_max_right _ _
  have hv_nn : ∀ i, 0 ≤ v i := fun i => le_max_right _ _
  have hdisj : ∀ i, u i * v i = 0 := by
    intro i
    simp only [hu, hv]
    rcases le_or_gt 0 (b i) with hh | hh
    · rw [max_eq_left hh, max_eq_right (by omega : -(b i) ≤ 0)]
      ring
    · rw [max_eq_right (by omega : b i ≤ 0), max_eq_left (by omega : 0 ≤ -(b i))]
      ring
  have hu_ne : u ≠ 0 := by
    intro h0
    have h1 : u ipos = 0 := by rw [h0]; rfl
    simp only [hu] at h1
    omega
  have hv_ne : v ≠ 0 := by
    intro h0
    have h1 : v ineg = 0 := by rw [h0]; rfl
    simp only [hv] at h1
    omega
  obtain ⟨iu, hiu⟩ : ∃ i, u i = 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv_ne
    exact ⟨i, (mul_eq_zero.mp (hdisj i)).resolve_right hi⟩
  obtain ⟨iv, hiv⟩ : ∃ i, v i = 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hu_ne
    exact ⟨i, (mul_eq_zero.mp (hdisj i)).resolve_left hi⟩
  have hdiag : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 + u 4 * v 4
      + u 5 * v 5 + u 6 * v 6 + u 7 * v 7 + u 8 * v 8 + u 9 * v 9 = 0 := by
    simp only [hdisj]
    ring
  have hsplit : quadC b = quadC u + quadC v
      + 2 * (u 0 * v 8 + v 0 * u 8 + u 0 * v 9 + v 0 * u 9
        + u 1 * v 3 + v 1 * u 3 + u 2 * v 4 + v 2 * u 4
        + u 3 * v 4 + v 3 * u 4 + u 4 * v 5 + v 4 * u 5
        + u 5 * v 6 + v 5 * u 6 + u 6 * v 7 + v 6 * u 7
        + u 7 * v 8 + v 7 * u 8) := by
    rw [hb_eq, quadC_sub, hdiag]
    ring
  have hcross_nn : ∀ x y : Fin 10 → ℤ, (∀ i, 0 ≤ x i) → (∀ i, 0 ≤ y i) →
      0 ≤ 2 * (x 0 * y 8 + y 0 * x 8 + x 0 * y 9 + y 0 * x 9
        + x 1 * y 3 + y 1 * x 3 + x 2 * y 4 + y 2 * x 4
        + x 3 * y 4 + y 3 * x 4 + x 4 * y 5 + y 4 * x 5
        + x 5 * y 6 + y 5 * x 6 + x 6 * y 7 + y 6 * x 7
        + x 7 * y 8 + y 7 * x 8) := by
    intro x y hx hy
    nlinarith [mul_nonneg (hx 0) (hy 8), mul_nonneg (hy 0) (hx 8),
      mul_nonneg (hx 0) (hy 9), mul_nonneg (hy 0) (hx 9),
      mul_nonneg (hx 1) (hy 3), mul_nonneg (hy 1) (hx 3),
      mul_nonneg (hx 2) (hy 4), mul_nonneg (hy 2) (hx 4),
      mul_nonneg (hx 3) (hy 4), mul_nonneg (hy 3) (hx 4),
      mul_nonneg (hx 4) (hy 5), mul_nonneg (hy 4) (hx 5),
      mul_nonneg (hx 5) (hy 6), mul_nonneg (hy 5) (hx 6),
      mul_nonneg (hx 6) (hy 7), mul_nonneg (hy 6) (hx 7),
      mul_nonneg (hx 7) (hy 8), mul_nonneg (hy 7) (hx 8)]
  have hU : 0 ≤ quadC u := quadC_nonneg_of_zero u iu hiu
  have hV : 0 ≤ quadC v := quadC_nonneg_of_zero v iv hiv
  have hT : 0 ≤ 2 * (u 0 * v 8 + v 0 * u 8 + u 0 * v 9 + v 0 * u 9
        + u 1 * v 3 + v 1 * u 3 + u 2 * v 4 + v 2 * u 4
        + u 3 * v 4 + v 3 * u 4 + u 4 * v 5 + v 4 * u 5
        + u 5 * v 6 + v 5 * u 6 + u 6 * v 7 + v 6 * u 7
        + u 7 * v 8 + v 7 * u 8) := hcross_nn u v hu_nn hv_nn
  have hU2 : quadC u = 0 ∨ 2 ≤ quadC u := by
    rcases eq_or_ne (quadC u) 0 with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      obtain ⟨c, hc⟩ := quadC_even u
      omega
  have hV2 : quadC v = 0 ∨ 2 ≤ quadC v := by
    rcases eq_or_ne (quadC v) 0 with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      obtain ⟨c, hc⟩ := quadC_even v
      omega
  rcases hU2 with hUz | hUp
  · -- `u` is a multiple of the null vector `δ`: then `v` is supported at the extra node, so the
    -- pairing across the edge `(0, 9)` alone contributes at least `2` to the form
    obtain ⟨k, hk⟩ : ∃ k : ℤ, u = k • e10NullVector := quadC_eq_zero_of_zero u iu hiu hUz
    have hk0 : u 0 = k := by rw [hk]; simp [e10NullVector]
    have huu : u = u 0 • e10NullVector := by
      rw [hk]
      have h1 : (k • e10NullVector : Fin 10 → ℤ) 0 = k := by simp [e10NullVector]
      rw [h1]
    have hu0 : 1 ≤ u 0 := by
      have h1 : u 0 ≠ 0 := by
        intro h0
        exact hu_ne (by rw [huu, h0, zero_smul])
      have h2 : 0 ≤ u 0 := hu_nn 0
      omega
    have hv9 : ∀ i, i ≠ 9 → v i = 0 := by
      intro i hi
      have hui : u i ≠ 0 := by
        rw [huu]
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_ne_zero (by omega) (ne_of_gt (e10NullVector_pos hi))
      exact (mul_eq_zero.mp (hdisj i)).resolve_left hui
    have hv9pos : 1 ≤ v 9 := by
      have h1 : v 9 ≠ 0 := by
        intro h0
        exact hv_ne (funext fun i => by
          by_cases hi : i = 9
          · rw [hi]; exact h0
          · exact hv9 i hi)
      have h2 : 0 ≤ v 9 := hv_nn 9
      omega
    have hV2' : 2 ≤ quadC v := by
      rcases hV2 with h | h
      · exact absurd h (by
          intro h0
          obtain ⟨k, hk⟩ : ∃ k : ℤ, v = k • e10NullVector := quadC_eq_zero_of_zero v iv hiv h0
          have h1 : v 9 = 0 := by rw [hk]; simp [e10NullVector]
          omega)
      · exact h
    have hT2 : 2 ≤ 2 * (u 0 * v 8 + v 0 * u 8 + u 0 * v 9 + v 0 * u 9
        + u 1 * v 3 + v 1 * u 3 + u 2 * v 4 + v 2 * u 4
        + u 3 * v 4 + v 3 * u 4 + u 4 * v 5 + v 4 * u 5
        + u 5 * v 6 + v 5 * u 6 + u 6 * v 7 + v 6 * u 7
        + u 7 * v 8 + v 7 * u 8) := by
      have h09 : 1 ≤ u 0 * v 9 := by nlinarith
      have h08 : 0 ≤ u 0 * v 8 := mul_nonneg (hu_nn 0) (hv_nn 8)
      have h80 : 0 ≤ v 0 * u 8 := mul_nonneg (hv_nn 0) (hu_nn 8)
      have h90 : 0 ≤ v 0 * u 9 := mul_nonneg (hv_nn 0) (hu_nn 9)
      have h13 : 0 ≤ u 1 * v 3 := mul_nonneg (hu_nn 1) (hv_nn 3)
      have h31 : 0 ≤ v 1 * u 3 := mul_nonneg (hv_nn 1) (hu_nn 3)
      have h24 : 0 ≤ u 2 * v 4 := mul_nonneg (hu_nn 2) (hv_nn 4)
      have h42 : 0 ≤ v 2 * u 4 := mul_nonneg (hv_nn 2) (hu_nn 4)
      have h34 : 0 ≤ u 3 * v 4 := mul_nonneg (hu_nn 3) (hv_nn 4)
      have h43 : 0 ≤ v 3 * u 4 := mul_nonneg (hv_nn 3) (hu_nn 4)
      have h45 : 0 ≤ u 4 * v 5 := mul_nonneg (hu_nn 4) (hv_nn 5)
      have h54 : 0 ≤ v 4 * u 5 := mul_nonneg (hv_nn 4) (hu_nn 5)
      have h56 : 0 ≤ u 5 * v 6 := mul_nonneg (hu_nn 5) (hv_nn 6)
      have h65 : 0 ≤ v 5 * u 6 := mul_nonneg (hv_nn 5) (hu_nn 6)
      have h67 : 0 ≤ u 6 * v 7 := mul_nonneg (hu_nn 6) (hv_nn 7)
      have h76 : 0 ≤ v 6 * u 7 := mul_nonneg (hv_nn 6) (hu_nn 7)
      have h78 : 0 ≤ u 7 * v 8 := mul_nonneg (hu_nn 7) (hv_nn 8)
      have h87 : 0 ≤ v 7 * u 8 := mul_nonneg (hv_nn 7) (hu_nn 8)
      linarith
    rw [hb] at hsplit
    linarith
  · rcases hV2 with hVz | hVp
    · obtain ⟨k, hk⟩ : ∃ k : ℤ, v = k • e10NullVector := quadC_eq_zero_of_zero v iv hiv hVz
      have hk0 : v 0 = k := by rw [hk]; simp [e10NullVector]
      have hvv : v = v 0 • e10NullVector := by
        rw [hk]
        have h1 : (k • e10NullVector : Fin 10 → ℤ) 0 = k := by simp [e10NullVector]
        rw [h1]
      have hv0 : 1 ≤ v 0 := by
        have h1 : v 0 ≠ 0 := by
          intro h0
          exact hv_ne (by rw [hvv, h0, zero_smul])
        have h2 : 0 ≤ v 0 := hv_nn 0
        omega
      have hu9 : ∀ i, i ≠ 9 → u i = 0 := by
        intro i hi
        have hvi : v i ≠ 0 := by
          rw [hvv]
          simp only [Pi.smul_apply, smul_eq_mul]
          exact mul_ne_zero (by omega) (ne_of_gt (e10NullVector_pos hi))
        exact (mul_eq_zero.mp (hdisj i)).resolve_right hvi
      have hu9pos : 1 ≤ u 9 := by
        have h1 : u 9 ≠ 0 := by
          intro h0
          exact hu_ne (funext fun i => by
            by_cases hi : i = 9
            · rw [hi]; exact h0
            · exact hu9 i hi)
        have h2 : 0 ≤ u 9 := hu_nn 9
        omega
      have hT2 : 2 ≤ 2 * (u 0 * v 8 + v 0 * u 8 + u 0 * v 9 + v 0 * u 9
          + u 1 * v 3 + v 1 * u 3 + u 2 * v 4 + v 2 * u 4
          + u 3 * v 4 + v 3 * u 4 + u 4 * v 5 + v 4 * u 5
          + u 5 * v 6 + v 5 * u 6 + u 6 * v 7 + v 6 * u 7
          + u 7 * v 8 + v 7 * u 8) := by
        have h09 : 1 ≤ v 0 * u 9 := by nlinarith
        have h08 : 0 ≤ u 0 * v 8 := mul_nonneg (hu_nn 0) (hv_nn 8)
        have h80 : 0 ≤ v 0 * u 8 := mul_nonneg (hv_nn 0) (hu_nn 8)
        have h09' : 0 ≤ u 0 * v 9 := mul_nonneg (hu_nn 0) (hv_nn 9)
        have h13 : 0 ≤ u 1 * v 3 := mul_nonneg (hu_nn 1) (hv_nn 3)
        have h31 : 0 ≤ v 1 * u 3 := mul_nonneg (hv_nn 1) (hu_nn 3)
        have h24 : 0 ≤ u 2 * v 4 := mul_nonneg (hu_nn 2) (hv_nn 4)
        have h42 : 0 ≤ v 2 * u 4 := mul_nonneg (hv_nn 2) (hu_nn 4)
        have h34 : 0 ≤ u 3 * v 4 := mul_nonneg (hu_nn 3) (hv_nn 4)
        have h43 : 0 ≤ v 3 * u 4 := mul_nonneg (hv_nn 3) (hu_nn 4)
        have h45 : 0 ≤ u 4 * v 5 := mul_nonneg (hu_nn 4) (hv_nn 5)
        have h54 : 0 ≤ v 4 * u 5 := mul_nonneg (hv_nn 4) (hu_nn 5)
        have h56 : 0 ≤ u 5 * v 6 := mul_nonneg (hu_nn 5) (hv_nn 6)
        have h65 : 0 ≤ v 5 * u 6 := mul_nonneg (hv_nn 5) (hu_nn 6)
        have h67 : 0 ≤ u 6 * v 7 := mul_nonneg (hu_nn 6) (hv_nn 7)
        have h76 : 0 ≤ v 6 * u 7 := mul_nonneg (hv_nn 6) (hu_nn 7)
        have h78 : 0 ≤ u 7 * v 8 := mul_nonneg (hu_nn 7) (hv_nn 8)
        have h87 : 0 ≤ v 7 * u 8 := mul_nonneg (hv_nn 7) (hu_nn 8)
        linarith
      rw [hb] at hsplit
      linarith
    · rw [hb] at hsplit
      linarith

end LeanCategories.Lattices.Valued

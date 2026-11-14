/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import LeanCategories.AlgebraicGeometry.HessianSingular
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.Order
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# The triple conic lies in the closure of the ten-nodal sextic stratum

This file proves that the cube of the smooth conic `Q = (X * Y + Z ^ 2 = 0)` lies in the
closure of the ten-nodal stratum `Σ_{10A_1}` — the set of nonzero sextic forms whose
projective singular locus is a set of ten points, each an ordinary node — in the topology
of coefficientwise convergence on ternary forms (`instCoeffTopologicalSpace`): the
top-level declaration is `tripleConic_mem_closure_tenNodalStratum`.

The degenerating family is the *Winger degeneration*
`H(t) = 27t³(X⁵Z + Y⁵Z) + X³Y³ + (729t⁶ + 18t² + 3)X²Y²Z² + (…)XYZ⁴ + (9t² + 1)⁵Z⁶`,
whose value at `t = 0` is the triple conic `(XY + Z²)³` and which, for every `t` with
`t ≠ 0` and `(3t - 2)(3t + 2)(4t² + 1)(9t² + 1) ≠ 0`, has exactly ten singular points,
all ordinary nodes (`wingerSingularLocus_card`, `wingerNode_rank`).

## Source

The Winger curve — the rational sextic with ten nodes whose degeneration to the triple
conic furnishes the family — is the pencil member `(λ : μ) = (27, 5)` of the pencil of
`A₅`-invariant sextics spanned by the triple conic, in Dolgachev, *Corrado Segre and nodal
cubic threefolds* (2018), §7, pp. 13–14; the pencil and Winger's equation
`27z(x⁵ + y⁵) + 5x³y³ + 150x²y²z² - 120xyz⁴ + 32z⁶ = 0` are at
`.tmp-sources/dolgachev-2018-arxiv-1604.02567v3.md:718-723`, the section at `:698`. The
reduction of the closure question to the cube of a smooth conic is Yu–Zheng,
arXiv:1809.06589v2, Prop. 3.7 (p. 10), `.tmp-sources/yu-zheng-2023-arxiv-1809.06589v2.md:553`.

## LC-09 search record

Corpus (via `scripts/formalization_corpus.py`, recorded in `.scratch/lc09-145b/`):
"hessian rank singular point ordinary node", "matrix rank submatrix minor nonzero",
"roots of unity cardinality complex fifth", "quadratic polynomial two distinct roots
discriminant", "projective space point equality scalar representative", "closure membership
convergent sequence degeneration family", "induced topology coefficientwise convergence
polynomial coefficients", "singular point homogeneous polynomial scaling invariant" — no
direct hit; nearest neighbours `TauCeti/LinearAlgebra/Matrix/Rank.lean` and
`TNLean/Algebra/ScalarThreeCocycle.lean` import Mathlib's `Matrix.Rank` and
`Projectivization` without adding declarations this file needs. Mathlib supplies everything
used: `Matrix.rank_submatrix_le` and `Matrix.rank_of_isUnit` (rank 2 at a node),
`hessianAt_rank_le_two_of_singular` (already in `HessianSingular.lean`),
`IsAlgClosed.exists_pow_nat_eq` (the square root of the discriminant),
`IsPrimitiveRoot.card_nthRootsFinset` with `Complex.isPrimitiveRoot_exp_of_coprime` (five
fifth roots of unity), `Projectivization.mk_eq_mk_iff'` (injectivity of the parameter map),
`mem_closure_of_tendsto`, `nhds_induced`, `Filter.tendsto_comap_iff`, `tendsto_pi_nhds` and
`tendsto_const_div_atTop_nhds_zero_nat` (the closure argument).

## Proof sketch

Each singular point of `V(H(t))` has `Z ≠ 0`; on the chart `Z = 1` the singular points
satisfy `x⁵ = y⁵` (Euler), so `x = ζy` with `ζ⁵ = 1`; writing `u = xy` one shows
`K(u) = u³ - cu² - 3du - 5f = 0` and `L(u) = g(u)² - 25a²u³ = 0` where `g(u) = 3u² + 2cu + d`.
Both `K` and `L` factor through the quadratic `q(u) = u² + (2 + 27t² - 729t⁶)u + (9t² + 1)⁴`,
whose two roots give, together with the five values of `ζ`, the ten singular points
`(ζy₀(u), y₀(u))` with `y₀ = -5aζ²u²/g(u)`.

At each of the ten points the Hessian minor `h_xx·h_yy - h_xy²` equals `-5·g(u)·(3u² - 2cu -
3d)` (`node_hessianMinor`; the proof clears the denominator `g(u)` of `y₀` and reduces the
three cleared entries modulo `ζ⁵ = 1` and `g(u)² = 25a²u³`), and both factors are nonzero
there (`node_g_ne_zero`, and `wingerBezout` forces `3u² - 2cu - 3d ≠ 0` at a root of `q` for
good `t`), so the Hessian has rank `2` (`wingerNode_rank`): an ordinary node.

Finally, the coefficients of `H(t)` are polynomial in `t`, so `t ↦ H(t)` is continuous in the
coefficientwise topology (`continuous_wingerFamily`), and every `t = 1/n` with `n ≥ 1` is
good (`wingerGood_one_div`); along this sequence the family lies in the stratum
(`wingerFamily_mem_tenNodalStratum`) and tends to `H(0) = Q³`, which is therefore in the
closure of the stratum (`mem_closure_of_tendsto`).
-/

namespace LeanCategories.AlgebraicGeometry

open MvPolynomial

/-! ## The Winger degeneration family -/

/-- The coefficient of `X⁵Z + Y⁵Z`. -/
def wA (t : ℂ) : ℂ := 27 * t ^ 3

/-- The coefficient of `X²Y²Z²`. -/
def wC (t : ℂ) : ℂ := 729 * t ^ 6 + 18 * t ^ 2 + 3

/-- The coefficient of `XYZ⁴`. -/
def wD (t : ℂ) : ℂ := -13122 * t ^ 8 - 2187 * t ^ 6 + 243 * t ^ 4 + 63 * t ^ 2 + 3

/-- The coefficient of `Z⁶`. -/
def wF (t : ℂ) : ℂ := (9 * t ^ 2 + 1) ^ 5

/-- The Winger degeneration family. -/
noncomputable def wingerFamily (t : ℂ) : MvPolynomial (Fin 3) ℂ :=
  C (wA t) * (X 0) ^ 5 * (X 2) ^ 1 + C (wA t) * (X 1) ^ 5 * (X 2) ^ 1
    + (X 0) ^ 3 * (X 1) ^ 3
    + C (wC t) * (X 0) ^ 2 * (X 1) ^ 2 * (X 2) ^ 2
    + C (wD t) * (X 0) ^ 1 * (X 1) ^ 1 * (X 2) ^ 4 + C (wF t) * (X 2) ^ 6

theorem wingerFamily_isHomogeneous (t : ℂ) : (wingerFamily t).IsHomogeneous 6 := by
  have h1 : (C (wA t) * (X (0 : Fin 3)) ^ 5 * (X (2 : Fin 3)) ^ 1 :
      MvPolynomial (Fin 3) ℂ).IsHomogeneous 6 := IsHomogeneous.mul
    (isHomogeneous_C_mul_X_pow _ 0 5) (isHomogeneous_X_pow 2 1)
  have h2 : (C (wA t) * (X (1 : Fin 3)) ^ 5 * (X (2 : Fin 3)) ^ 1 :
      MvPolynomial (Fin 3) ℂ).IsHomogeneous 6 := IsHomogeneous.mul
    (isHomogeneous_C_mul_X_pow _ 1 5) (isHomogeneous_X_pow 2 1)
  have h3 : ((X (0 : Fin 3)) ^ 3 * (X (1 : Fin 3)) ^ 3 :
      MvPolynomial (Fin 3) ℂ).IsHomogeneous 6 := IsHomogeneous.mul
    (isHomogeneous_X_pow 0 3) (isHomogeneous_X_pow 1 3)
  have h4 : (C (wC t) * (X (0 : Fin 3)) ^ 2 * (X (1 : Fin 3)) ^ 2 * (X 2) ^ 2 :
      MvPolynomial (Fin 3) ℂ).IsHomogeneous 6 := IsHomogeneous.mul
    (IsHomogeneous.mul (isHomogeneous_C_mul_X_pow _ 0 2) (isHomogeneous_X_pow 1 2))
    (isHomogeneous_X_pow 2 2)
  have h5 : (C (wD t) * (X (0 : Fin 3)) ^ 1 * (X (1 : Fin 3)) ^ 1 * (X (2 : Fin 3)) ^ 4 :
      MvPolynomial (Fin 3) ℂ).IsHomogeneous 6 := IsHomogeneous.mul
    (IsHomogeneous.mul (isHomogeneous_C_mul_X_pow _ 0 1) (isHomogeneous_X_pow 1 1))
    (isHomogeneous_X_pow 2 4)
  have h6 : (C (wF t) * (X (2 : Fin 3)) ^ 6 :
      MvPolynomial (Fin 3) ℂ).IsHomogeneous 6 := isHomogeneous_C_mul_X_pow _ 2 6
  unfold wingerFamily
  exact IsHomogeneous.add (IsHomogeneous.add (IsHomogeneous.add (IsHomogeneous.add
    (IsHomogeneous.add h1 h2) h3) h4) h5) h6

theorem eval_wingerFamily (t : ℂ) (v : Fin 3 → ℂ) :
    eval v (wingerFamily t) =
      wA t * (v 0 ^ 5 + v 1 ^ 5) * v 2 + v 0 ^ 3 * v 1 ^ 3
        + wC t * v 0 ^ 2 * v 1 ^ 2 * v 2 ^ 2 + wD t * v 0 * v 1 * v 2 ^ 4
        + wF t * v 2 ^ 6 := by
  simp only [wingerFamily, map_add]
  simp
  ring

theorem wingerFamily_ne_zero (t : ℂ) : wingerFamily t ≠ 0 := by
  intro h
  have h1 := eval_wingerFamily t ![1, 1, 0]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_pow, mul_one] at h1
  norm_num at h1
  rw [h] at h1
  simp at h1

theorem wingerFamily_zero : wingerFamily 0 = (X 0 * X 1 + (X 2) ^ 2) ^ 3 := by
  refine MvPolynomial.funext (fun v => ?_)
  simp only [eval_pow, eval_mul, eval_add, eval_X]
  rw [eval_wingerFamily 0 v]
  simp only [wA, wC, wD, wF]
  norm_num
  ring

/-! ## The affine chart `Z = 1` -/

/-- The dehomogenization of the Winger family on the chart `Z = 1`. -/
def wH (t x y : ℂ) : ℂ :=
  wA t * (x ^ 5 + y ^ 5) + x ^ 3 * y ^ 3 + wC t * x ^ 2 * y ^ 2 + wD t * x * y + wF t

/-- `∂/∂X` of `wH`. -/
def wHx (t x y : ℂ) : ℂ :=
  5 * wA t * x ^ 4 + 3 * x ^ 2 * y ^ 3 + 2 * wC t * x * y ^ 2 + wD t * y

/-- `∂/∂Y` of `wH`. -/
def wHy (t x y : ℂ) : ℂ :=
  5 * wA t * y ^ 4 + 3 * x ^ 3 * y ^ 2 + 2 * wC t * x ^ 2 * y + wD t * x

/-- `∂/∂Z` of the family, evaluated at `Z = 1`. -/
def wHz (t x y : ℂ) : ℂ :=
  wA t * (x ^ 5 + y ^ 5) + 2 * wC t * x ^ 2 * y ^ 2 + 4 * wD t * x * y + 6 * wF t

/-- The second derivative `∂²/∂X²` of `wH`. -/
def wHxx (t x y : ℂ) : ℂ := 20 * wA t * x ^ 3 + 6 * x * y ^ 3 + 2 * wC t * y ^ 2

/-- The second derivative `∂²/∂Y²` of `wH`. -/
def wHyy (t x y : ℂ) : ℂ := 20 * wA t * y ^ 3 + 6 * x ^ 3 * y + 2 * wC t * x ^ 2

/-- The mixed second derivative `∂²/∂X∂Y` of `wH`. -/
def wHxy (t x y : ℂ) : ℂ := 9 * x ^ 2 * y ^ 2 + 4 * wC t * x * y + wD t

private theorem pderiv_natCast' (i : Fin 3) (n : ℕ) :
    pderiv i ((n : ℕ) : MvPolynomial (Fin 3) ℂ) = 0 := by
  rw [show ((n : ℕ) : MvPolynomial (Fin 3) ℂ) = C ((n : ℕ) : ℂ) from by
    simp [map_natCast], pderiv_C]

theorem eval_pderiv_wingerFamily_zero (t : ℂ) (v : Fin 3 → ℂ) :
    eval v (pderiv 0 (wingerFamily t)) =
      5 * wA t * v 0 ^ 4 * v 2 + 3 * v 0 ^ 2 * v 1 ^ 3 + 2 * wC t * v 0 * v 1 ^ 2 * v 2 ^ 2
        + wD t * v 1 * v 2 ^ 4 := by
  simp only [wingerFamily, map_add, map_add, map_add, map_add, map_add, pderiv_mul, pderiv_pow,
    pderiv_C, pderiv_X_self, pderiv_X_of_ne, mul_zero, add_zero, zero_add, pderiv_natCast']
  simp
  ring

theorem eval_pderiv_wingerFamily_one (t : ℂ) (v : Fin 3 → ℂ) :
    eval v (pderiv 1 (wingerFamily t)) =
      5 * wA t * v 1 ^ 4 * v 2 + 3 * v 0 ^ 3 * v 1 ^ 2 + 2 * wC t * v 0 ^ 2 * v 1 * v 2 ^ 2
        + wD t * v 0 * v 2 ^ 4 := by
  simp only [wingerFamily, map_add, map_add, map_add, map_add, map_add, pderiv_mul, pderiv_pow,
    pderiv_C, pderiv_X_self, pderiv_X_of_ne, mul_zero, add_zero, zero_add, pderiv_natCast']
  simp
  ring

theorem eval_pderiv_wingerFamily_two (t : ℂ) (v : Fin 3 → ℂ) :
    eval v (pderiv 2 (wingerFamily t)) =
      wA t * (v 0 ^ 5 + v 1 ^ 5) + 2 * wC t * v 0 ^ 2 * v 1 ^ 2 * v 2
        + 4 * wD t * v 0 * v 1 * v 2 ^ 3 + 6 * wF t * v 2 ^ 5 := by
  simp only [wingerFamily, map_add, map_add, map_add, map_add, map_add, pderiv_mul, pderiv_pow,
    pderiv_C, pderiv_X_self, pderiv_X_of_ne, mul_zero, add_zero, zero_add, pderiv_natCast']
  simp
  ring

theorem eval_pderiv2_wingerFamily_00 (t x y : ℂ) :
    eval ![x, y, 1] (pderiv 0 (pderiv 0 (wingerFamily t))) = wHxx t x y := by
  simp only [wingerFamily, wHxx, map_add, map_add, map_add, map_add, map_add, map_add, map_add,
    map_add, map_add, map_add, map_add, pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self,
    pderiv_X_of_ne, mul_zero, add_zero, zero_add, pderiv_natCast']
  simp
  ring

theorem eval_pderiv2_wingerFamily_11 (t x y : ℂ) :
    eval ![x, y, 1] (pderiv 1 (pderiv 1 (wingerFamily t))) = wHyy t x y := by
  simp only [wingerFamily, wHyy, map_add, map_add, map_add, map_add, map_add, map_add, map_add,
    map_add, map_add, map_add, map_add, pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self,
    pderiv_X_of_ne, mul_zero, add_zero, zero_add, pderiv_natCast']
  simp
  ring

theorem eval_pderiv2_wingerFamily_01 (t x y : ℂ) :
    eval ![x, y, 1] (pderiv 0 (pderiv 1 (wingerFamily t))) = wHxy t x y := by
  simp only [wingerFamily, wHxy, map_add, map_add, map_add, map_add, map_add, map_add, map_add,
    map_add, map_add, map_add, map_add, pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self,
    pderiv_X_of_ne, mul_zero, add_zero, zero_add, pderiv_natCast']
  simp
  ring

theorem eval_pderiv2_wingerFamily_10 (t x y : ℂ) :
    eval ![x, y, 1] (pderiv 1 (pderiv 0 (wingerFamily t))) = wHxy t x y := by
  simp only [wingerFamily, wHxy, map_add, map_add, map_add, map_add, map_add, map_add, map_add,
    map_add, map_add, map_add, map_add, pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self,
    pderiv_X_of_ne, mul_zero, add_zero, zero_add, pderiv_natCast']
  simp
  ring

/-! ## The auxiliary polynomials `g`, `K`, `L`, `q` -/

/-- `g(u) = 3u² + 2cu + d`, the shared mixed part of the first derivatives. -/
def wG (t u : ℂ) : ℂ := 3 * u ^ 2 + 2 * wC t * u + wD t

/-- The cubic satisfied by `u = xy` at a singular point. -/
def wK (t u : ℂ) : ℂ := u ^ 3 - wC t * u ^ 2 - 3 * wD t * u - 5 * wF t

/-- The quartic `g(u)² - 25a²u³` satisfied by `u = xy` at a singular point. -/
def wL (t u : ℂ) : ℂ := (wG t u) ^ 2 - 25 * (wA t) ^ 2 * u ^ 3

/-- The quadratic through whose roots the singular values of `u = xy` run. -/
def wQ (t u : ℂ) : ℂ := u ^ 2 + (2 + 27 * t ^ 2 - 729 * t ^ 6) * u + (9 * t ^ 2 + 1) ^ 4

/-- The cofactor of `wQ` in the factorization of `wL`. -/
def wQ2 (t u : ℂ) : ℂ :=
  u ^ 2 + (2 - 3 * t ^ 2 - 324 * t ^ 6) * u
    + (2916 * t ^ 8 - 324 * t ^ 6 - 99 * t ^ 4 + 6 * t ^ 2 + 1)

/-- The node factor of the Hessian minor: `3u² - 2cu - 3d`. -/
def wFp (t u : ℂ) : ℂ := 3 * u ^ 2 - 2 * wC t * u - 3 * wD t

theorem wingerK_factor (t u : ℂ) : wK t u = (u - 45 * t ^ 2 - 5) * wQ t u := by
  simp only [wK, wQ, wC, wD, wF]
  ring

theorem wingerL_factor (t u : ℂ) : wL t u = 9 * wQ2 t u * wQ t u := by
  simp only [wL, wQ, wQ2, wG, wA, wC, wD]
  ring

theorem wingerQ2_special (t : ℂ) :
    wQ2 t (45 * t ^ 2 + 5)
      = -9 * (3 * t - 2) * (3 * t + 2) * (4 * t ^ 2 + 1) ^ 2 * (9 * t ^ 2 + 1) := by
  simp only [wQ2]
  ring

theorem wingerDisc (t u : ℂ) :
    (2 * u + (2 + 27 * t ^ 2 - 729 * t ^ 6)) ^ 2 - 4 * wQ t u
      = 9 * t ^ 2 * (3 * t - 2) * (3 * t + 2) * (9 * t ^ 2 + 1) ^ 4 := by
  simp only [wQ]
  ring

theorem wingerBezout (t u : ℂ) :
    (-4374 * t ^ 8 - 1458 * t ^ 6 - 351 * t ^ 4 + 9 * t ^ 2 * u - 108 * t ^ 2 + 3 * u - 9)
        * wQ t u
      + (2187 * t ^ 8 + 729 * t ^ 6 - 3 * t ^ 2 * u - 15 * t ^ 2 - u - 1) * wFp t u
      = 27 * t ^ 2 * (3 * t - 2) * (3 * t + 2) * (4 * t ^ 2 + 1) * (9 * t ^ 2 + 1) ^ 5 := by
  simp only [wQ, wFp, wC, wD]
  ring

theorem wingerK_zero (t : ℂ) : wK t 0 = -5 * wF t := by
  simp only [wK]
  ring

theorem wingerL_rel (t u : ℂ) (h : wL t u = 0) : (wG t u) ^ 2 = 25 * (wA t) ^ 2 * u ^ 3 :=
  eq_of_sub_eq_zero (by simpa only [wL] using h)

/-! ## The Euler identities -/

theorem wingerEuler (t x y : ℂ) :
    6 * wH t x y = x * wHx t x y + y * wHy t x y + wHz t x y := by
  simp only [wH, wHx, wHy, wHz]
  ring

theorem wingerDiff (t x y : ℂ) :
    x * wHx t x y - y * wHy t x y = 5 * wA t * (x ^ 5 - y ^ 5) := by
  simp only [wHx, wHy]
  ring

theorem wingerHx_prod (t x y : ℂ) :
    x * wHx t x y = 5 * wA t * x ^ 5 + (x * y) * wG t (x * y) := by
  simp only [wHx, wG]
  ring

theorem wingerHxG (t x y : ℂ) : wHx t x y = 5 * wA t * x ^ 4 + y * (wG t (x * y)) := by
  simp only [wHx, wG]
  ring

theorem wingerKcombo (t x y : ℂ) :
    (x * wHx t x y + y * wHy t x y) - 5 * wHz t x y = 6 * wK t (x * y) := by
  simp only [wHx, wHy, wHz, wK]
  ring

/-! ## Homogeneous evaluation under scaling -/

theorem eval_smul_of_isHomogeneous {F : MvPolynomial (Fin 3) ℂ} {n : ℕ}
    (hF : F.IsHomogeneous n) (v : Fin 3 → ℂ) (c : ℂ) :
    eval (c • v) F = c ^ n * eval v F := by
  classical
  have hsum : ∀ d ∈ F.support, (∑ i, d i) = n := by
    intro d hd
    have h1 : Finsupp.weight 1 d = n := hF (mem_support_iff.1 hd)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype d (fun i c => c • (1 : Fin 3 → ℕ) i)
      (fun _ => zero_smul ℕ _)] at h1
    simpa using h1
  rw [eval_eq', eval_eq']
  have hstep : ∑ d ∈ F.support, F.coeff d * ∏ i, (c • v) i ^ d i
      = ∑ d ∈ F.support, c ^ n * (F.coeff d * ∏ i, v i ^ d i) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hprod : ∏ i, (c • v) i ^ d i = c ^ (∑ i, d i) * ∏ i, v i ^ d i := by
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
      rw [Finset.prod_pow_eq_pow_sum]
    rw [hprod, hsum d hd]; ring
  rw [hstep, ← Finset.mul_sum]

/-! ## Chart reduction -/

/-! ## Chart reduction -/

theorem singular_z_ne_zero (t : ℂ) (ht : t ≠ 0) (v : Fin 3 → ℂ) (hv : v ≠ 0)
    (hs : IsSingularPoint (wingerFamily t) v) : v 2 ≠ 0 := by
  intro h0
  have hF : eval v (wingerFamily t) = 0 := hs.1
  rw [eval_wingerFamily t v, h0] at hF
  norm_num at hF
  have hp := hs.2 2
  rw [eval_pderiv_wingerFamily_two t v, h0] at hp
  norm_num at hp
  rcases hF with hv0 | hv1
  · have hv1 : v 1 ≠ 0 := by
      intro hh; apply hv; funext i; fin_cases i <;> simp [hv0, hh, h0]
    rw [hv0] at hp; norm_num at hp
    rcases hp with h' | h'
    · exact ht ((pow_eq_zero_iff (by norm_num)).1
        ((mul_eq_zero.1 h').resolve_left (by norm_num)))
    · exact hv1 h' 
  · have hv0 : v 0 ≠ 0 := by
      intro hh; apply hv; funext i; fin_cases i <;> simp [hv1, hh, h0]
    rw [hv1] at hp; norm_num at hp
    rcases hp with h' | h'
    · exact ht ((pow_eq_zero_iff (by norm_num)).1
        ((mul_eq_zero.1 h').resolve_left (by norm_num)))
    · exact hv0 h' 

theorem eval_wingerFamily_chart (t x y : ℂ) :
    eval ![x, y, 1] (wingerFamily t) = wH t x y := by
  rw [eval_wingerFamily t ![x, y, 1]]
  simp [wH]

theorem singular_iff_affine (t x y : ℂ) :
    IsSingularPoint (wingerFamily t) ![x, y, 1] ↔
      wHx t x y = 0 ∧ wHy t x y = 0 ∧ wHz t x y = 0 := by
  constructor
  · intro hs
    refine ⟨?_, ?_, ?_⟩
    · have hx := hs.2 0
      rw [eval_pderiv_wingerFamily_zero t ![x, y, 1]] at hx
      simpa [wHx] using hx
    · have hy := hs.2 1
      rw [eval_pderiv_wingerFamily_one t ![x, y, 1]] at hy
      simpa [wHy] using hy
    · have hz := hs.2 2
      rw [eval_pderiv_wingerFamily_two t ![x, y, 1]] at hz
      simpa [wHz] using hz
  · rintro ⟨hx, hy, hz⟩
    have hE : wH t x y = 0 := by
      have e := wingerEuler t x y
      rw [hx, hy, hz] at e
      have e0 : 6 * wH t x y = 0 := by linear_combination e
      exact (mul_eq_zero.1 e0).resolve_left (by norm_num)
    have e0 : eval ![x, y, 1] (pderiv 0 (wingerFamily t)) = 0 := by
      rw [eval_pderiv_wingerFamily_zero t ![x, y, 1]]
      simpa [wHx] using hx
    have e1 : eval ![x, y, 1] (pderiv ((0 : Fin 2).succ) (wingerFamily t)) = 0 := by
      show eval ![x, y, 1] (pderiv 1 (wingerFamily t)) = 0
      rw [eval_pderiv_wingerFamily_one t ![x, y, 1]]
      simpa [wHy] using hy
    have e2 : ∀ i' : Fin 1, eval ![x, y, 1] (pderiv (i'.succ.succ) (wingerFamily t)) = 0 := by
      intro i'
      have hi : i' = 0 := Subsingleton.elim _ _
      subst hi
      show eval ![x, y, 1] (pderiv 2 (wingerFamily t)) = 0
      rw [eval_pderiv_wingerFamily_two t ![x, y, 1]]
      simpa [wHz] using hz
    refine ⟨eval_wingerFamily_chart t x y ▸ hE, fun j => ?_⟩
    exact Fin.cases e0 (fun i => Fin.cases e1 e2 i) j

/-! ## The upper bound: singular points on the chart satisfy `wQ t (x * y) = 0` -/

theorem singular_affine_upper (t : ℂ) (ht : t ≠ 0) (hf : wF t ≠ 0)
    (hgood : (3 * t - 2) * (3 * t + 2) * (4 * t ^ 2 + 1) * (9 * t ^ 2 + 1) ≠ 0) (x y : ℂ)
    (hs : wHx t x y = 0 ∧ wHy t x y = 0 ∧ wHz t x y = 0) :
    x ^ 5 = y ^ 5 ∧ wQ t (x * y) = 0 := by
  obtain ⟨hx, hy, hz⟩ := hs
  have hwA : wA t ≠ 0 := by
    intro h
    rw [wA] at h
    exact ht ((pow_eq_zero_iff (by norm_num)).1
      ((mul_eq_zero.1 h).resolve_left (by norm_num)))
  have hdiff : x ^ 5 = y ^ 5 := by
    have h := wingerDiff t x y
    rw [hx, hy] at h
    have h0 : 5 * wA t * (x ^ 5 - y ^ 5) = 0 := by linear_combination -h
    have h3 := (mul_eq_zero.1 h0).resolve_left (mul_ne_zero (by norm_num) hwA)
    exact sub_eq_zero.1 h3
  refine ⟨hdiff, ?_⟩
  have hK : wK t (x * y) = 0 := by
    have h := wingerKcombo t x y
    rw [hx, hy, hz] at h
    have h0 : 6 * wK t (x * y) = 0 := by linear_combination -h
    exact (mul_eq_zero.1 h0).resolve_left (by norm_num)
  have hu : x * y ≠ 0 := by
    intro hxy
    rw [hxy] at hK
    rw [wingerK_zero] at hK
    exact hf ((mul_eq_zero.1 hK).resolve_left (by norm_num))
  have hL : wL t (x * y) = 0 := by
    have hgp := wingerHx_prod t x y
    rw [hx] at hgp
    have e1 : (5 * wA t * x ^ 5) ^ 2 = ((x * y) * wG t (x * y)) ^ 2 := by
      linear_combination ((x * y) * wG t (x * y) - 5 * wA t * x ^ 5) * hgp
    have e2 : (5 * wA t * x ^ 5) ^ 2 = (x * y) ^ 2 * (25 * wA t ^ 2 * (x * y) ^ 3) := by
      linear_combination (5 * wA t * x ^ 5) * (5 * wA t) * hdiff
    have key : ((x * y) * wG t (x * y)) ^ 2 = (x * y) ^ 2 * (25 * wA t ^ 2 * (x * y) ^ 3) := by
      linear_combination e2 - e1
    have hne : (x * y) ^ 2 ≠ 0 := fun hh => hu (sq_eq_zero_iff.1 hh)
    have key' : (x * y) ^ 2 * (wG t (x * y)) ^ 2
        = (x * y) ^ 2 * (25 * wA t ^ 2 * (x * y) ^ 3) := by linear_combination key
    have hgg : (wG t (x * y)) ^ 2 = 25 * wA t ^ 2 * (x * y) ^ 3 :=
      mul_left_cancel₀ hne key'
    simp only [wL]
    linear_combination hgg
  by_contra hq
  have hKf : (x * y - 45 * t ^ 2 - 5) * wQ t (x * y) = 0 := by
    rw [← wingerK_factor t (x * y)]
    exact hK
  have hxy5 : x * y = 45 * t ^ 2 + 5 := by
    linear_combination (mul_eq_zero.1 hKf).resolve_right hq
  have hQ2 : wQ2 t (x * y) = 0 := by
    have hLf : 9 * wQ2 t (x * y) * wQ t (x * y) = 0 := by
      rw [← wingerL_factor t (x * y)]
      exact hL
    exact (mul_eq_zero.1 ((mul_eq_zero.1 hLf).resolve_right hq)).resolve_left (by norm_num)
  have hA : (3 * t - 2) ≠ 0 := by intro h; apply hgood; rw [h]; ring
  have hB : (3 * t + 2) ≠ 0 := by intro h; apply hgood; rw [h]; ring
  have hC : (4 * t ^ 2 + 1) ≠ 0 := by intro h; apply hgood; rw [h]; ring
  have hD : (9 * t ^ 2 + 1) ≠ 0 := by intro h; apply hgood; rw [h]; ring
  have hfinal : -9 * (3 * t - 2) * (3 * t + 2) * (4 * t ^ 2 + 1) ^ 2 * (9 * t ^ 2 + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hA) hB)
      (pow_ne_zero 2 hC)) hD
  rw [hxy5] at hQ2
  rw [wingerQ2_special t] at hQ2
  exact hfinal hQ2

/-! ## The node construction -/

/-- The numerator of `nodeY`. -/
def nodeN (t ζ u : ℂ) : ℂ := -5 * wA t * ζ ^ 2 * u ^ 2

/-- The node construction: `y₀ = -5aζ²u²/g(u)`. -/
noncomputable def nodeY (t ζ u : ℂ) : ℂ := nodeN t ζ u / (wG t u)

theorem nodeY_eq (t ζ u : ℂ) : nodeY t ζ u = nodeN t ζ u / (wG t u) := rfl

theorem wQ_root_wK (t u : ℂ) (hu : wQ t u = 0) : wK t u = 0 := by
  rw [wingerK_factor, hu]; ring

theorem wQ_root_wL (t u : ℂ) (hu : wQ t u = 0) : wL t u = 0 := by
  rw [wingerL_factor, hu]; ring

theorem wQ_root_g_sq (t u : ℂ) (hu : wQ t u = 0) : (wG t u) ^ 2 = 25 * (wA t) ^ 2 * u ^ 3 :=
  wingerL_rel t u (wQ_root_wL t u hu)

theorem node_zeta_ne (ζ : ℂ) (hζ : ζ ^ 5 = 1) : ζ ≠ 0 := by
  intro h
  rw [h, zero_pow (by norm_num : (5 : ℕ) ≠ 0)] at hζ
  exact absurd hζ (by norm_num)

theorem node_g_ne_zero (t u : ℂ) (hu : wQ t u = 0) (ha : wA t ≠ 0) (hu_ne : u ≠ 0) :
    wG t u ≠ 0 := by
  intro h
  have hg2 : (wG t u) ^ 2 = 25 * (wA t) ^ 2 * u ^ 3 := wQ_root_g_sq t u hu
  rw [h] at hg2
  norm_num at hg2
  rcases hg2 with h' | h'
  · exact ha h'
  · exact hu_ne h' 

theorem node_zeta_sq (t ζ u : ℂ) (hζ : ζ ^ 5 = 1) (hu : wQ t u = 0) (ha : wA t ≠ 0)
    (hu_ne : u ≠ 0) : ζ * (nodeY t ζ u) ^ 2 = u := by
  have hg2 : (wG t u) ^ 2 = 25 * (wA t) ^ 2 * u ^ 3 := wQ_root_g_sq t u hu
  have hg : wG t u ≠ 0 := node_g_ne_zero t u hu ha hu_ne
  have key : ζ * (-5 * wA t * ζ ^ 2 * u ^ 2) ^ 2 = u * (wG t u) ^ 2 := by
    linear_combination 25 * (wA t) ^ 2 * u ^ 4 * hζ - u * hg2
  rw [nodeY_eq, div_pow, ← mul_div_assoc, div_eq_iff (pow_ne_zero 2 hg)]
  exact key

theorem nodeY_ne_zero (t ζ u : ℂ) (hζ : ζ ^ 5 = 1) (hu : wQ t u = 0) (ha : wA t ≠ 0)
    (hu_ne : u ≠ 0) : nodeY t ζ u ≠ 0 := by
  have hg : wG t u ≠ 0 := node_g_ne_zero t u hu ha hu_ne
  rw [nodeY_eq]
  intro h
  rcases (div_eq_zero_iff.1 h) with h' | h'
  · simp only [nodeN] at h'
    have h1 := (mul_eq_zero.1 h').resolve_left (by
      intro hh
      have h2 := (mul_eq_zero.1 hh).resolve_left (mul_ne_zero (by norm_num : (-5 : ℂ) ≠ 0) ha)
      exact node_zeta_ne ζ hζ ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).1 h2))
    exact hu_ne ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).1 h1)
  · exact hg h'

theorem node_sing (t ζ u : ℂ) (hζ : ζ ^ 5 = 1) (hu : wQ t u = 0) (ha : wA t ≠ 0)
    (hu_ne : u ≠ 0) :
    wHx t (ζ * nodeY t ζ u) (nodeY t ζ u) = 0 ∧ wHy t (ζ * nodeY t ζ u) (nodeY t ζ u) = 0
      ∧ wHz t (ζ * nodeY t ζ u) (nodeY t ζ u) = 0 := by
  have hg : wG t u ≠ 0 := node_g_ne_zero t u hu ha hu_ne
  have hζy : ζ * (nodeY t ζ u) ^ 2 = u := node_zeta_sq t ζ u hζ hu ha hu_ne
  have hy_ne : nodeY t ζ u ≠ 0 := nodeY_ne_zero t ζ u hζ hu ha hu_ne
  have hxy : (ζ * nodeY t ζ u) * nodeY t ζ u = u := by
    linear_combination hζy
  have hx4 : (ζ * nodeY t ζ u) ^ 4 = ζ ^ 2 * u ^ 2 := by
    linear_combination (ζ ^ 2 * (ζ * (nodeY t ζ u) ^ 2 + u)) * hζy
  have hx5 : (ζ * nodeY t ζ u) ^ 5 = (nodeY t ζ u) ^ 5 := by
    rw [mul_pow, hζ]
    ring
  have hx : wHx t (ζ * nodeY t ζ u) (nodeY t ζ u) = 0 := by
    rw [wingerHxG, hxy, hx4, nodeY_eq, div_mul_cancel₀ _ hg]
    simp only [nodeN]
    ring
  have hy : wHy t (ζ * nodeY t ζ u) (nodeY t ζ u) = 0 := by
    have hdd := wingerDiff t (ζ * nodeY t ζ u) (nodeY t ζ u)
    rw [hx5, hx, mul_zero, zero_sub] at hdd
    have hzero : nodeY t ζ u * wHy t (ζ * nodeY t ζ u) (nodeY t ζ u) = 0 := by
      linear_combination -hdd
    exact (mul_eq_zero.1 hzero).resolve_left hy_ne
  have hz : wHz t (ζ * nodeY t ζ u) (nodeY t ζ u) = 0 := by
    have hc := wingerKcombo t (ζ * nodeY t ζ u) (nodeY t ζ u)
    rw [hxy, wQ_root_wK t u hu, hx, hy] at hc
    have h5 : (5 : ℂ) * wHz t (ζ * nodeY t ζ u) (nodeY t ζ u) = 0 := by
      linear_combination -hc
    exact (mul_eq_zero.1 h5).resolve_left (by norm_num)
  exact ⟨hx, hy, hz⟩

/-! ## The classification of affine singular points -/

theorem wA_ne_zero_of (t : ℂ) (ht : t ≠ 0) : wA t ≠ 0 := by
  intro h
  rw [wA] at h
  exact ht ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).1
    ((mul_eq_zero.1 h).resolve_left (by norm_num)))

theorem wQ_zero_ne (t : ℂ) (hD : 9 * t ^ 2 + 1 ≠ 0) : wQ t 0 ≠ 0 := by
  intro h
  simp only [wQ] at h
  norm_num at h
  exact hD h

theorem singular_affine_classify (t : ℂ) (ht : t ≠ 0) (hf : wF t ≠ 0)
    (hgood : (3 * t - 2) * (3 * t + 2) * (4 * t ^ 2 + 1) * (9 * t ^ 2 + 1) ≠ 0) (x y : ℂ) :
    (wHx t x y = 0 ∧ wHy t x y = 0 ∧ wHz t x y = 0) ↔
      ∃ u ζ, wQ t u = 0 ∧ ζ ^ 5 = 1 ∧ x = ζ * nodeY t ζ u ∧ y = nodeY t ζ u := by
  have ha : wA t ≠ 0 := wA_ne_zero_of t ht
  have hD : 9 * t ^ 2 + 1 ≠ 0 := by
    intro h; apply hgood; rw [h]; ring
  constructor
  · intro hs
    obtain ⟨hdiff, hQ⟩ := singular_affine_upper t ht hf hgood x y hs
    have hu_ne : x * y ≠ 0 := by
      intro h0
      rw [h0] at hQ
      exact absurd hQ (wQ_zero_ne t hD)
    have hy_ne : y ≠ 0 := fun h0 => hu_ne (by rw [h0]; ring)
    have hg : wG t (x * y) ≠ 0 := node_g_ne_zero t (x * y) hQ ha hu_ne
    have hx0 : 5 * wA t * x ^ 4 + y * wG t (x * y) = 0 := by
      rw [← wingerHxG]
      exact hs.1
    have hN : nodeN t (x / y) (x * y) = -5 * wA t * x ^ 4 := by
      unfold nodeN
      field_simp
    have hy_node : y = nodeY t (x / y) (x * y) := by
      rw [nodeY_eq, hN, eq_comm, div_eq_iff hg]
      linear_combination -hx0
    refine ⟨x * y, x / y, hQ, ?_, ?_, hy_node⟩
    · rw [div_pow, div_eq_one_iff_eq (pow_ne_zero 5 hy_ne)]
      exact hdiff
    · rw [← hy_node]
      field_simp
  · rintro ⟨u, ζ, hu, hζ, rfl, rfl⟩
    exact node_sing t ζ u hζ hu ha (fun h0 => (wQ_zero_ne t hD) (by rw [h0] at hu; exact hu))

/-! ## The singular locus of the projective curve -/

/-- The set of singular points of `V(wingerFamily t)` in `ℙ²`. -/
def wingerSingularLocus (t : ℂ) :
    Set (Projectivization ℂ (Fin 3 → ℂ)) :=
  {p | ∃ v : Fin 3 → ℂ, ∃ (_hv : v ≠ 0), p = Projectivization.mk ℂ v _hv
    ∧ IsSingularPoint (wingerFamily t) v}

/-! ## The good set of parameters -/

/-- The good parameters: `t ≠ 0` and the four factors appearing in `wingerQ2_special`,
`wingerDisc` and `wingerBezout`. For every good `t` the curve `V(wingerFamily t)` has
exactly ten singular points, all ordinary nodes. -/
def WingerGood (t : ℂ) : Prop :=
  t ≠ 0 ∧ (3 * t - 2) * (3 * t + 2) * (4 * t ^ 2 + 1) * (9 * t ^ 2 + 1) ≠ 0

theorem WingerGood.ht {t : ℂ} (h : WingerGood t) : t ≠ 0 := h.1

theorem WingerGood.wA_ne {t : ℂ} (h : WingerGood t) : wA t ≠ 0 := wA_ne_zero_of t h.1

theorem WingerGood.hgood {t : ℂ} (h : WingerGood t) :
    (3 * t - 2) * (3 * t + 2) * (4 * t ^ 2 + 1) * (9 * t ^ 2 + 1) ≠ 0 := h.2

theorem WingerGood.wF_ne {t : ℂ} (h : WingerGood t) : wF t ≠ 0 := by
  have h9 : 9 * t ^ 2 + 1 ≠ 0 := fun hc => h.2 (by rw [hc]; ring)
  unfold wF
  exact pow_ne_zero 5 h9

theorem WingerGood.factors_ne {t : ℂ} (h : WingerGood t) :
    (3 * t - 2) ≠ 0 ∧ (3 * t + 2) ≠ 0 ∧ (4 * t ^ 2 + 1) ≠ 0
      ∧ (9 * t ^ 2 + 1) ≠ 0 := by
  refine ⟨fun hc => h.2 ?_, fun hc => h.2 ?_, fun hc => h.2 ?_, fun hc => h.2 ?_⟩ <;>
    rw [hc] <;> ring

/-- The discriminant of the quadratic `wQ t`; by `wingerDisc` it is nonzero exactly when
`wQ t` has two distinct roots. -/
def wDisc (t : ℂ) : ℂ := 9 * t ^ 2 * (3 * t - 2) * (3 * t + 2) * (9 * t ^ 2 + 1) ^ 4

theorem WingerGood.wDisc_ne {t : ℂ} (h : WingerGood t) : wDisc t ≠ 0 := by
  obtain ⟨f1, f2, f3, f4⟩ := h.factors_ne
  have h9 : 9 * t ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 h.1)
  unfold wDisc
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h9 f1) f2) (pow_ne_zero 4 f4)

/-- A good `t` gives two distinct roots of `wQ t`, and every root is one of them. -/
theorem wQ_two_roots {t : ℂ} (hd : wDisc t ≠ 0) :
    ∃ u₁ u₂ : ℂ, u₁ ≠ u₂ ∧ ∀ u, wQ t u = 0 ↔ u = u₁ ∨ u = u₂ := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (wDisc t) (by norm_num : 0 < 2)
  have hwne : w ≠ 0 := by
    intro hc
    rw [hc] at hw
    exact hd (by rw [← hw, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
  refine ⟨(w - (2 + 27 * t ^ 2 - 729 * t ^ 6)) / 2,
    (-w - (2 + 27 * t ^ 2 - 729 * t ^ 6)) / 2, ?_, ?_⟩
  · intro h
    apply hwne
    linear_combination h
  · intro u
    have hiff : wQ t u = 0 ↔ (2 * u + (2 + 27 * t ^ 2 - 729 * t ^ 6)) ^ 2 = wDisc t := by
      simp only [wDisc]
      constructor
      · intro hu
        linear_combination wingerDisc t u + 4 * hu
      · intro h
        linear_combination (h - wingerDisc t u) / 4
    rw [hiff, ← hw]
    constructor
    · intro h
      have hm : (2 * u + (2 + 27 * t ^ 2 - 729 * t ^ 6) - w)
          * (2 * u + (2 + 27 * t ^ 2 - 729 * t ^ 6) + w) = 0 := by linear_combination h
      rcases mul_eq_zero.1 hm with h' | h'
      · exact Or.inl (by linear_combination h' / 2)
      · exact Or.inr (by linear_combination h' / 2)
    · rintro (rfl | rfl)
      · ring
      · ring

/-- The node factor `wFp` is nonzero at every root of `wQ t` for good `t`: the cleared
Bézout relation `wingerBezout` forces it. -/
theorem wFp_ne_zero_of_wQ {t : ℂ} (u : ℂ) (hu : wQ t u = 0) (ht : t ≠ 0)
    (hgood : (3 * t - 2) * (3 * t + 2) * (4 * t ^ 2 + 1) * (9 * t ^ 2 + 1) ≠ 0) :
    wFp t u ≠ 0 := by
  intro h
  have hb := wingerBezout t u
  rw [hu, h] at hb
  simp only [mul_zero, add_zero] at hb
  obtain ⟨f1, f2, f3, f4⟩ := WingerGood.factors_ne ⟨ht, hgood⟩
  exact absurd hb.symm (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht)) f1) f2) f3) (pow_ne_zero 5 f4))

/-! ## The node condition: the Hessian minor -/

/-- The cleared `X`-Hessian at the node: `(wG t u) ^ 4 • h_xx` at `(ζ * y₀, y₀)`, with
`y₀ = nodeY t ζ u`, as a polynomial in the node parameters. -/
def hessXXn (t ζ u : ℂ) : ℂ :=
  20 * wA t * ζ ^ 3 * (nodeN t ζ u) ^ 3 * wG t u + 6 * ζ * (nodeN t ζ u) ^ 4
    + 2 * wC t * (nodeN t ζ u) ^ 2 * (wG t u) ^ 2

/-- The cleared `Y`-Hessian at the node. -/
def hessYYn (t ζ u : ℂ) : ℂ :=
  20 * wA t * (nodeN t ζ u) ^ 3 * wG t u + 6 * ζ ^ 3 * (nodeN t ζ u) ^ 4
    + 2 * wC t * ζ ^ 2 * (nodeN t ζ u) ^ 2 * (wG t u) ^ 2

/-- The cleared mixed Hessian at the node. -/
def hessXYn (t ζ u : ℂ) : ℂ :=
  9 * ζ ^ 2 * (nodeN t ζ u) ^ 4 + 4 * wC t * ζ * (nodeN t ζ u) ^ 2 * (wG t u) ^ 2
    + wD t * (wG t u) ^ 4

private theorem hessXXn_eq (t ζ u : ℂ) (hg : wG t u ≠ 0) :
    (wG t u) ^ 4 * wHxx t (ζ * nodeY t ζ u) (nodeY t ζ u) = hessXXn t ζ u := by
  simp only [nodeY_eq, wHxx, hessXXn]
  field_simp

private theorem hessYYn_eq (t ζ u : ℂ) (hg : wG t u ≠ 0) :
    (wG t u) ^ 4 * wHyy t (ζ * nodeY t ζ u) (nodeY t ζ u) = hessYYn t ζ u := by
  simp only [nodeY_eq, wHyy, hessYYn]
  field_simp

private theorem hessXYn_eq (t ζ u : ℂ) (hg : wG t u ≠ 0) :
    (wG t u) ^ 4 * wHxy t (ζ * nodeY t ζ u) (nodeY t ζ u) = hessXYn t ζ u := by
  simp only [nodeY_eq, wHxy, hessXYn]
  field_simp

/-- The Hessian minor at a constructed node equals `-5 • g(u) • (3u² - 2cu - 3d)`, the
product of the two factors that are nonzero at the node (`node_g_ne_zero` for `g(u)` and
`wFp_ne_zero_of_wQ` for `3u² - 2cu - 3d`). The proof clears the denominator `g(u)` of
`y₀ = -5aζ²u²/g(u)` and reduces the three cleared entries modulo the two relations
`ζ ^ 5 = 1` and `g(u) ^ 2 = 25a²u³` that hold at the node (`node_zeta_sq`,
`wQ_root_g_sq`); the reductions are the three congruences `e1`, `e2`, `e3` below. -/
theorem node_hessianMinor (t ζ u : ℂ) (hζ : ζ ^ 5 = 1) (hu : wQ t u = 0) (ha : wA t ≠ 0)
    (hu_ne : u ≠ 0) :
    wHxx t (ζ * nodeY t ζ u) (nodeY t ζ u) * wHyy t (ζ * nodeY t ζ u) (nodeY t ζ u)
      - (wHxy t (ζ * nodeY t ζ u) (nodeY t ζ u)) ^ 2 = -5 * wG t u * wFp t u := by
  have hg : wG t u ≠ 0 := node_g_ne_zero t u hu ha hu_ne
  have hζne : ζ ≠ 0 := node_zeta_ne ζ hζ
  have hR : (wG t u) ^ 2 = 25 * (wA t) ^ 2 * u ^ 3 := wQ_root_g_sq t u hu
  have hXX := hessXXn_eq t ζ u hg
  have hYY := hessYYn_eq t ζ u hg
  have hXY := hessXYn_eq t ζ u hg
  have e1 : ζ * hessXXn t ζ u = (-4 * wG t u + 6 * u ^ 2 + 2 * wC t * u) * (wG t u) ^ 4
      + (ζ ^ 5 - 1) * (-2500 * (wA t) ^ 4 * (ζ ^ 5 + 1) * u ^ 6 * wG t u
          + 3750 * (wA t) ^ 4 * (ζ ^ 5 + 1) * u ^ 8
          + 50 * (wA t) ^ 2 * wC t * u ^ 4 * (wG t u) ^ 2)
      + ((wG t u) ^ 2 - 25 * (wA t) ^ 2 * u ^ 3) * (4 * (wG t u) ^ 3
          - 2 * wC t * u * (wG t u) ^ 2 - 6 * u ^ 2 * (wG t u) ^ 2
          + 100 * (wA t) ^ 2 * u ^ 3 * wG t u - 150 * (wA t) ^ 2 * u ^ 5) := by
    simp only [hessXXn, nodeN]
    ring
  have e2 : hessYYn t ζ u = ζ * (-4 * wG t u + 6 * u ^ 2 + 2 * wC t * u) * (wG t u) ^ 4
      + (ζ ^ 5 - 1) * (ζ * (-2500 * (wA t) ^ 4 * (ζ ^ 5 + 1) * u ^ 6 * wG t u
          + 3750 * (wA t) ^ 4 * (ζ ^ 5 + 1) * u ^ 8
          + 50 * (wA t) ^ 2 * wC t * u ^ 4 * (wG t u) ^ 2)
          + 2500 * (wA t) ^ 4 * ζ ^ 6 * u ^ 6 * wG t u)
      + ((wG t u) ^ 2 - 25 * (wA t) ^ 2 * u ^ 3) * (ζ * (4 * (wG t u) ^ 3
          - 2 * wC t * u * (wG t u) ^ 2 - 6 * u ^ 2 * (wG t u) ^ 2
          + 100 * (wA t) ^ 2 * u ^ 3 * wG t u - 150 * (wA t) ^ 2 * u ^ 5)) := by
    simp only [hessYYn, nodeN]
    ring
  have e3 : hessXYn t ζ u = (9 * u ^ 2 + 4 * wC t * u + wD t) * (wG t u) ^ 4
      + (ζ ^ 5 - 1) * (5625 * (wA t) ^ 4 * (ζ ^ 5 + 1) * u ^ 8
          + 100 * (wA t) ^ 2 * wC t * u ^ 4 * (wG t u) ^ 2)
      + ((wG t u) ^ 2 - 25 * (wA t) ^ 2 * u ^ 3) * (-(4 * wC t * u + 9 * u ^ 2)
          * (wG t u) ^ 2 - 225 * (wA t) ^ 2 * u ^ 5) := by
    simp only [hessXYn, nodeN]
    ring
  rw [hζ, hR] at e1 e2 e3
  simp only [sub_self, zero_mul, add_zero] at e1 e2 e3
  have hAB : (-4 * wG t u + 6 * u ^ 2 + 2 * wC t * u) ^ 2
      - (9 * u ^ 2 + 4 * wC t * u + wD t) ^ 2 = -5 * wG t u * wFp t u := by
    simp only [wG, wFp]
    ring
  have key : ζ * (hessXXn t ζ u * hessYYn t ζ u - (hessXYn t ζ u) ^ 2)
      = ζ * ((-4 * wG t u + 6 * u ^ 2 + 2 * wC t * u) ^ 2
          - (9 * u ^ 2 + 4 * wC t * u + wD t) ^ 2) * (wG t u) ^ 8 := by
    rw [mul_sub, ← mul_assoc, e1, e2, e3]
    ring
  have s1 : (wG t u) ^ 8 * (wHxx t (ζ * nodeY t ζ u) (nodeY t ζ u)
        * wHyy t (ζ * nodeY t ζ u) (nodeY t ζ u)
        - (wHxy t (ζ * nodeY t ζ u) (nodeY t ζ u)) ^ 2)
      = hessXXn t ζ u * hessYYn t ζ u - (hessXYn t ζ u) ^ 2 := by
    rw [← hXX, ← hYY, ← hXY]
    ring
  have s2 : ζ * (wG t u) ^ 8 * (wHxx t (ζ * nodeY t ζ u) (nodeY t ζ u)
        * wHyy t (ζ * nodeY t ζ u) (nodeY t ζ u)
        - (wHxy t (ζ * nodeY t ζ u) (nodeY t ζ u)) ^ 2)
      = ζ * (-5 * wG t u * wFp t u) * (wG t u) ^ 8 := by
    linear_combination ζ * s1 + key + ζ * (wG t u) ^ 8 * hAB
  refine mul_left_cancel₀ (mul_ne_zero hζne (pow_ne_zero 8 hg)) ?_
  linear_combination s2

/-- The Hessian minor at a constructed node is nonzero: the point is an ordinary node. -/
theorem node_hessianMinor_ne (t ζ u : ℂ) (hζ : ζ ^ 5 = 1) (hu : wQ t u = 0) (ha : wA t ≠ 0)
    (hu_ne : u ≠ 0) (ht : t ≠ 0)
    (hgood : (3 * t - 2) * (3 * t + 2) * (4 * t ^ 2 + 1) * (9 * t ^ 2 + 1) ≠ 0) :
    wHxx t (ζ * nodeY t ζ u) (nodeY t ζ u) * wHyy t (ζ * nodeY t ζ u) (nodeY t ζ u)
      - (wHxy t (ζ * nodeY t ζ u) (nodeY t ζ u)) ^ 2 ≠ 0 := by
  rw [node_hessianMinor t ζ u hζ hu ha hu_ne]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (node_g_ne_zero t u hu ha hu_ne))
    (wFp_ne_zero_of_wQ u hu ht hgood)

/-! ## The nodes as projective points -/

/-- The affine representative of the node parameterized by `(u, ζ)`. -/
noncomputable def nodeVec (t u ζ : ℂ) : Fin 3 → ℂ := ![ζ * nodeY t ζ u, nodeY t ζ u, 1]

theorem nodeVec_ne_zero (t u ζ : ℂ) : nodeVec t u ζ ≠ 0 := by
  intro h
  have h2 := congrFun h 2
  simp only [nodeVec, Matrix.cons_val_two] at h2
  exact one_ne_zero h2

/-- The projective point of the parameter pair `(u, ζ)`: `[ζ • y₀(u) : y₀(u) : 1]`. -/
noncomputable def wingerNodePoint (t u ζ : ℂ) : Projectivization ℂ (Fin 3 → ℂ) :=
  Projectivization.mk ℂ (nodeVec t u ζ) (nodeVec_ne_zero t u ζ)

theorem wingerNode_isSingularPoint (t ζ u : ℂ) (hζ : ζ ^ 5 = 1) (hu : wQ t u = 0)
    (ha : wA t ≠ 0) (hu_ne : u ≠ 0) : IsSingularPoint (wingerFamily t) (nodeVec t u ζ) := by
  simp only [nodeVec]
  exact singular_iff_affine t (ζ * nodeY t ζ u) (nodeY t ζ u) |>.mpr
    (node_sing t ζ u hζ hu ha hu_ne)

/-- Singularity of a projective point of `V(wingerFamily t)` does not depend on the
affine representative. -/
theorem isSingularPoint_smul (t c : ℂ) (hc : c ≠ 0) (v : Fin 3 → ℂ) :
    IsSingularPoint (wingerFamily t) (c • v) ↔ IsSingularPoint (wingerFamily t) v := by
  have h6 : eval (c • v) (wingerFamily t) = c ^ 6 * eval v (wingerFamily t) :=
    eval_smul_of_isHomogeneous (wingerFamily_isHomogeneous t) v c
  have h5 : ∀ j : Fin 3, eval (c • v) (pderiv j (wingerFamily t))
      = c ^ 5 * eval v (pderiv j (wingerFamily t)) :=
    fun j => eval_smul_of_isHomogeneous ((wingerFamily_isHomogeneous t).pderiv (i := j)) v c
  constructor
  · rintro ⟨hF, hp⟩
    rw [h6] at hF
    exact ⟨(mul_eq_zero.1 hF).resolve_left (pow_ne_zero 6 hc), fun j =>
      (mul_eq_zero.1 (by rw [← h5 j]; exact hp j)).resolve_left (pow_ne_zero 5 hc)⟩
  · rintro ⟨hF, hp⟩
    exact ⟨by rw [h6, hF, mul_zero], fun j => by rw [h5 j, hp j, mul_zero]⟩

/-- At a singular point of a ternary form whose Hessian has an invertible top-left
`2 × 2` block, the Hessian has rank exactly `2`: the block gives rank at least `2`, and
`hessianAt_rank_le_two_of_singular` gives at most `2`. -/
theorem hessianAt_rank_eq_two {F : MvPolynomial (Fin 3) ℂ} {n : ℕ} {v : Fin 3 → ℂ}
    (hF : F.IsHomogeneous n) (hs : IsSingularPoint F v) (hv : v ≠ 0)
    (hdet : ((hessianAt F v).submatrix (![0, 1] : Fin 2 → Fin 3)
        (![0, 1] : Fin 2 → Fin 3)).det ≠ 0) :
    (hessianAt F v).rank = 2 := by
  have hrk2 : ((hessianAt F v).submatrix (![0, 1] : Fin 2 → Fin 3)
      (![0, 1] : Fin 2 → Fin 3)).rank = 2 := by
    have h : IsUnit ((hessianAt F v).submatrix (![0, 1] : Fin 2 → Fin 3)
        (![0, 1] : Fin 2 → Fin 3)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    simpa using Matrix.rank_of_isUnit _ h
  exact le_antisymm (hessianAt_rank_le_two_of_singular hF hs hv)
    (by rw [← hrk2]; exact Matrix.rank_submatrix_le _ _ _)

/-- Every constructed node of `V(wingerFamily t)` is a singular point at which the
Hessian has rank `2` — an ordinary node. -/
theorem wingerNode_rank (t ζ u : ℂ) (hζ : ζ ^ 5 = 1) (hu : wQ t u = 0) (ha : wA t ≠ 0)
    (hu_ne : u ≠ 0) (ht : t ≠ 0)
    (hgood : (3 * t - 2) * (3 * t + 2) * (4 * t ^ 2 + 1) * (9 * t ^ 2 + 1) ≠ 0) :
    (hessianAt (wingerFamily t) (nodeVec t u ζ)).rank = 2 := by
  have hsing := wingerNode_isSingularPoint t ζ u hζ hu ha hu_ne
  have hminor : (wHxx t (ζ * nodeY t ζ u) (nodeY t ζ u) * wHyy t (ζ * nodeY t ζ u)
        (nodeY t ζ u) - (wHxy t (ζ * nodeY t ζ u) (nodeY t ζ u)) ^ 2) ≠ 0 :=
    node_hessianMinor_ne t ζ u hζ hu ha hu_ne ht hgood
  refine hessianAt_rank_eq_two (wingerFamily_isHomogeneous t) hsing
    (nodeVec_ne_zero t u ζ) ?_
  have hBdet : ((hessianAt (wingerFamily t) (nodeVec t u ζ)).submatrix
      (![0, 1] : Fin 2 → Fin 3) (![0, 1] : Fin 2 → Fin 3)).det
      = wHxx t (ζ * nodeY t ζ u) (nodeY t ζ u) * wHyy t (ζ * nodeY t ζ u) (nodeY t ζ u)
        - (wHxy t (ζ * nodeY t ζ u) (nodeY t ζ u)) ^ 2 := by
    simp only [Matrix.det_fin_two, hessianAt, Matrix.submatrix, Matrix.of_apply, nodeVec,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [eval_pderiv2_wingerFamily_00, eval_pderiv2_wingerFamily_11,
      eval_pderiv2_wingerFamily_01, eval_pderiv2_wingerFamily_10]
    ring
  rw [hBdet]
  exact hminor

/-! ## The projective singular locus -/

theorem vec_one_ne_zero (x y : ℂ) : (![x, y, 1] : Fin 3 → ℂ) ≠ 0 := by
  intro h
  have h2 := congrFun h 2
  simp only [Matrix.cons_val_two] at h2
  exact one_ne_zero h2

/-- The projective singular locus of `V(wingerFamily t)` for good `t` is exactly the set
of ten constructed points: every singular point has `Z ≠ 0` (`singular_z_ne_zero`), so it
is represented on the chart `Z = 1` and classified by `singular_affine_classify`. -/
theorem wingerSingularLocus_char (t : ℂ) (g : WingerGood t)
    (p : Projectivization ℂ (Fin 3 → ℂ)) :
    p ∈ wingerSingularLocus t ↔
      ∃ u ζ, wQ t u = 0 ∧ ζ ^ 5 = 1 ∧ p = wingerNodePoint t u ζ := by
  obtain ⟨ht, hgood⟩ := g
  have hf : wF t ≠ 0 := WingerGood.wF_ne ⟨ht, hgood⟩
  have ha : wA t ≠ 0 := WingerGood.wA_ne ⟨ht, hgood⟩
  have h9 : 9 * t ^ 2 + 1 ≠ 0 := fun hc => hgood (by rw [hc]; ring)
  constructor
  · rintro ⟨v, hv, hpv, hsing⟩
    have hv2 : v 2 ≠ 0 := singular_z_ne_zero t ht v hv hsing
    have hscale : v = (v 2) • ![v 0 / v 2, v 1 / v 2, 1] := by
      funext i
      fin_cases i
      · simp [mul_div_cancel₀ _ hv2]
      · simp [mul_div_cancel₀ _ hv2]
      · simp
    have hmk : p = Projectivization.mk ℂ ![v 0 / v 2, v 1 / v 2, 1] (vec_one_ne_zero _ _) := by
      rw [hpv]
      exact (Projectivization.mk_eq_mk_iff' ℂ v ![v 0 / v 2, v 1 / v 2, 1] hv
        (vec_one_ne_zero _ _)).mpr ⟨v 2, hscale.symm⟩
    have hsing' : IsSingularPoint (wingerFamily t) ![v 0 / v 2, v 1 / v 2, 1] := by
      rw [← isSingularPoint_smul t (v 2) hv2 ![v 0 / v 2, v 1 / v 2, 1], ← hscale]
      exact hsing
    obtain ⟨hx, hy, hz⟩ := (singular_iff_affine t (v 0 / v 2) (v 1 / v 2)).mp hsing'
    obtain ⟨u, ζ, hu, hζ, hxe, hye⟩ :=
      (singular_affine_classify t ht hf hgood (v 0 / v 2) (v 1 / v 2)).mp ⟨hx, hy, hz⟩
    refine ⟨u, ζ, hu, hζ, ?_⟩
    rw [hmk, hxe, hye]
    rfl
  · rintro ⟨u, ζ, hu, hζ, rfl⟩
    have hu_ne : u ≠ 0 := fun h0 => wQ_zero_ne t h9 (by rw [h0] at hu; exact hu)
    exact ⟨nodeVec t u ζ, nodeVec_ne_zero t u ζ, rfl,
      wingerNode_isSingularPoint t ζ u hζ hu ha hu_ne⟩

/-- Distinct parameter pairs give distinct projective points. -/
theorem wingerNodePoint_inj (t : ℂ) (g : WingerGood t) {u₁ u₂ ζ₁ ζ₂ : ℂ}
    (hu₁ : wQ t u₁ = 0) (hζ₁ : ζ₁ ^ 5 = 1) (hu₂ : wQ t u₂ = 0) (hζ₂ : ζ₂ ^ 5 = 1)
    (hEq : wingerNodePoint t u₁ ζ₁ = wingerNodePoint t u₂ ζ₂) :
    u₁ = u₂ ∧ ζ₁ = ζ₂ := by
  obtain ⟨ht, hgood⟩ := g
  have h9 : 9 * t ^ 2 + 1 ≠ 0 := fun hc => hgood (by rw [hc]; ring)
  have ha : wA t ≠ 0 := WingerGood.wA_ne ⟨ht, hgood⟩
  have hu₁ne : u₁ ≠ 0 := fun h0 => wQ_zero_ne t h9 (by rw [h0] at hu₁; exact hu₁)
  have hu₂ne : u₂ ≠ 0 := fun h0 => wQ_zero_ne t h9 (by rw [h0] at hu₂; exact hu₂)
  obtain ⟨a, ha'⟩ :=
    (Projectivization.mk_eq_mk_iff' ℂ (nodeVec t u₁ ζ₁) (nodeVec t u₂ ζ₂)
      (nodeVec_ne_zero t u₁ ζ₁) (nodeVec_ne_zero t u₂ ζ₂)).mp hEq
  have ha1 : a = 1 := by
    simpa [nodeVec] using congrFun ha' 2
  have hvec : nodeVec t u₂ ζ₂ = nodeVec t u₁ ζ₁ := by
    rw [← ha', ha1, one_smul]
  have h0 := congrFun hvec 0
  have h1 := congrFun hvec 1
  simp only [nodeVec, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hy1 : nodeY t ζ₁ u₁ ≠ 0 := nodeY_ne_zero t ζ₁ u₁ hζ₁ hu₁ ha hu₁ne
  have hy2 : nodeY t ζ₂ u₂ ≠ 0 := nodeY_ne_zero t ζ₂ u₂ hζ₂ hu₂ ha hu₂ne
  have hζ : ζ₂ = ζ₁ := by
    rw [h1] at h0
    exact mul_right_cancel₀ hy1 h0
  refine ⟨?_, hζ.symm⟩
  have e1 := node_zeta_sq t ζ₁ u₁ hζ₁ hu₁ ha hu₁ne
  have e2 := node_zeta_sq t ζ₂ u₂ hζ₂ hu₂ ha hu₂ne
  rw [h1, hζ] at e2
  rw [← e2, e1]

/-- For good `t`, the projective singular locus of `V(wingerFamily t)` is a finite set
of ten points: the products of the two roots of `wQ t` with the five fifth roots of
unity (`wingerDisc` gives two distinct roots, `IsPrimitiveRoot.card_nthRootsFinset`
five fifth roots of unity, and `wingerNodePoint_inj` injectivity). -/
theorem wingerSingularLocus_card (t : ℂ) (g : WingerGood t) :
    ∃ s : Finset (Projectivization ℂ (Fin 3 → ℂ)),
      s.card = 10 ∧ ∀ p, p ∈ s ↔ p ∈ wingerSingularLocus t := by
  classical
  obtain ⟨u₁, u₂, hne, hchar⟩ := wQ_two_roots (WingerGood.wDisc_ne g)
  have hprim := Complex.isPrimitiveRoot_exp_of_coprime 1 5 (by norm_num) (by decide)
  have hzcard : (Polynomial.nthRootsFinset 5 (1 : ℂ)).card = 5 :=
    IsPrimitiveRoot.card_nthRootsFinset hprim
  set S : Finset (ℂ × ℂ) := insert u₁ ({u₂} : Finset ℂ) ×ˢ
    Polynomial.nthRootsFinset 5 (1 : ℂ) with hS
  have hne' : u₁ ∉ ({u₂} : Finset ℂ) := Finset.notMem_singleton.mpr hne
  have hScard : S.card = 10 := by
    rw [hS, Finset.card_product, Finset.card_insert_of_notMem hne', Finset.card_singleton,
      hzcard]
  have hSmem : ∀ pr : ℂ × ℂ, pr ∈ S ↔ (wQ t pr.1 = 0 ∧ pr.2 ^ 5 = 1) := by
    intro pr
    rw [hS, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
      Polynomial.mem_nthRootsFinset (by norm_num : 0 < 5)]
    constructor
    · rintro ⟨h1 | h1, hζ⟩
      · exact ⟨by rw [h1]; exact (hchar u₁).mpr (Or.inl rfl), hζ⟩
      · exact ⟨by rw [h1]; exact (hchar u₂).mpr (Or.inr rfl), hζ⟩
    · rintro ⟨hu, hζ⟩
      rcases (hchar pr.1).mp hu with h1 | h1
      · exact ⟨Or.inl h1, hζ⟩
      · exact ⟨Or.inr h1, hζ⟩
  refine ⟨S.image (fun pr => wingerNodePoint t pr.1 pr.2), ?_, ?_⟩
  · refine (Finset.card_image_of_injOn ?_).trans hScard
    intro pr₁ hpr₁ pr₂ hpr₂ hEq
    have c₁ := (hSmem pr₁).mp hpr₁
    have c₂ := (hSmem pr₂).mp hpr₂
    obtain ⟨huc, hzc⟩ := wingerNodePoint_inj t g c₁.1 c₁.2 c₂.1 c₂.2 hEq
    exact Prod.ext huc hzc
  · intro p
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨pr, hpr, rfl⟩
      have c := (hSmem pr).mp hpr
      exact (wingerSingularLocus_char t g (wingerNodePoint t pr.1 pr.2)).mpr
        ⟨pr.1, pr.2, c.1, c.2, rfl⟩
    · intro hp
      obtain ⟨u, ζ, hu, hζ, rfl⟩ := (wingerSingularLocus_char t g p).mp hp
      exact ⟨(u, ζ), (hSmem (u, ζ)).mpr ⟨hu, hζ⟩, rfl⟩

/-! ## The ten-nodal stratum -/

/-- The set of singular points of `V(F)` in `ℙ²`, for a ternary form `F`. -/
noncomputable def singularLocus (F : MvPolynomial (Fin 3) ℂ) :
    Set (Projectivization ℂ (Fin 3 → ℂ)) :=
  {p | ∃ v, ∃ _hv : v ≠ 0, p = Projectivization.mk ℂ v _hv ∧ IsSingularPoint F v}

theorem wingerSingularLocus_eq_singularLocus (t : ℂ) :
    wingerSingularLocus t = singularLocus (wingerFamily t) := rfl

/-- `p` is an ordinary node of `F`: some representative `v` of `p` is a singular point of
`F` at which the Hessian of `F` has rank `2`, the maximal rank at a singular point of a
ternary form (`hessianAt_rank_le_two_of_singular`); equivalently, the quadratic part of
the Taylor expansion of `F` is nondegenerate on the tangent space `ℂ³ / ℂ • v`. -/
def IsOrdinaryNode (F : MvPolynomial (Fin 3) ℂ) (p : Projectivization ℂ (Fin 3 → ℂ)) :
    Prop :=
  ∃ v, ∃ _hv : v ≠ 0, p = Projectivization.mk ℂ v _hv ∧ IsSingularPoint F v
    ∧ (hessianAt F v).rank = 2

/-- Membership in the ten-nodal stratum `Σ_{10A_1}` of the space of ternary sextic
forms: `F` is a nonzero sextic whose projective singular locus is a set of ten points,
each an ordinary node. -/
def IsTenNodalSextic (F : MvPolynomial (Fin 3) ℂ) : Prop :=
  F.IsHomogeneous 6 ∧ F ≠ 0 ∧ ∃ s : Finset (Projectivization ℂ (Fin 3 → ℂ)),
    s.card = 10 ∧ (∀ p, p ∈ s ↔ p ∈ singularLocus F)
      ∧ ∀ p ∈ singularLocus F, IsOrdinaryNode F p

/-- The ten-nodal stratum itself. -/
def TenNodalStratum : Set (MvPolynomial (Fin 3) ℂ) := {F | IsTenNodalSextic F}

theorem wingerFamily_mem_tenNodalStratum (t : ℂ) (g : WingerGood t) :
    wingerFamily t ∈ TenNodalStratum := by
  obtain ⟨ht, hgood⟩ := g
  have ha : wA t ≠ 0 := WingerGood.wA_ne ⟨ht, hgood⟩
  have h9 : 9 * t ^ 2 + 1 ≠ 0 := fun hc => hgood (by rw [hc]; ring)
  obtain ⟨s, hscard, hs⟩ := wingerSingularLocus_card t ⟨ht, hgood⟩
  rw [wingerSingularLocus_eq_singularLocus] at hs
  refine ⟨wingerFamily_isHomogeneous t, wingerFamily_ne_zero t, s, hscard, hs, ?_⟩
  intro p hp
  obtain ⟨u, ζ, hu, hζ, rfl⟩ := (wingerSingularLocus_char t ⟨ht, hgood⟩ p).mp hp
  have hu_ne : u ≠ 0 := fun h0 => wQ_zero_ne t h9 (by rw [h0] at hu; exact hu)
  exact ⟨nodeVec t u ζ, nodeVec_ne_zero t u ζ, rfl,
    wingerNode_isSingularPoint t ζ u hζ hu ha hu_ne,
    wingerNode_rank t ζ u hζ hu ha hu_ne ht hgood⟩

/-! ## The coefficientwise topology and the closure -/

/-- The topology of coefficientwise convergence on ternary forms: the initial topology
for the coefficient functionals `F ↦ F.coeff d`. The coefficients determine the form, so
the topology is Hausdorff (the instance below), and on the finite-dimensional space of
sextic forms it is the standard one. -/
noncomputable instance instCoeffTopologicalSpace : TopologicalSpace (MvPolynomial (Fin 3) ℂ) :=
  TopologicalSpace.induced (fun F d => F.coeff d) Pi.topologicalSpace

instance : T2Space (MvPolynomial (Fin 3) ℂ) := by
  refine T2Space.of_injective_continuous (f := fun F d => F.coeff d) ?_ ?_
  · intro x y h
    have hc : x.coeff = y.coeff := Finsupp.ext fun d => congrFun h d
    calc x = AddMonoidAlgebra.ofCoeff x.coeff := (AddMonoidAlgebra.ofCoeff_coeff x).symm
      _ = AddMonoidAlgebra.ofCoeff y.coeff := by rw [hc]
      _ = y := AddMonoidAlgebra.ofCoeff_coeff y
  · exact continuous_induced_dom

/-- The exponent vectors of the six monomials of `wingerFamily`. -/
noncomputable def wMon1 : (Fin 3 →₀ ℕ) := Finsupp.single 0 5 + Finsupp.single 2 1

/-- The exponent vector of `Y⁵Z`. -/
noncomputable def wMon2 : (Fin 3 →₀ ℕ) := Finsupp.single 1 5 + Finsupp.single 2 1

/-- The exponent vector of `X³Y³`. -/
noncomputable def wMon3 : (Fin 3 →₀ ℕ) := Finsupp.single 0 3 + Finsupp.single 1 3

/-- The exponent vector of `X²Y²Z²`. -/
noncomputable def wMon4 : (Fin 3 →₀ ℕ) :=
  Finsupp.single 0 2 + Finsupp.single 1 2 + Finsupp.single 2 2

/-- The exponent vector of `XYZ⁴`. -/
noncomputable def wMon5 : (Fin 3 →₀ ℕ) :=
  Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 4

/-- The exponent vector of `Z⁶`. -/
noncomputable def wMon6 : (Fin 3 →₀ ℕ) := Finsupp.single 2 6

theorem wingerFamily_eq_monomials (t : ℂ) :
    wingerFamily t = MvPolynomial.monomial wMon1 (wA t) + MvPolynomial.monomial wMon2 (wA t)
      + MvPolynomial.monomial wMon3 1 + MvPolynomial.monomial wMon4 (wC t)
      + MvPolynomial.monomial wMon5 (wD t) + MvPolynomial.monomial wMon6 (wF t) := by
  simp only [wingerFamily, wMon1, wMon2, wMon3, wMon4, wMon5, wMon6, X_pow_eq_monomial,
    monomial_mul_monomial, C_mul_monomial, mul_one]

theorem coeff_wingerFamily (d : Fin 3 →₀ ℕ) (t : ℂ) :
    (wingerFamily t).coeff d =
      (if wMon1 = d then wA t else 0) + (if wMon2 = d then wA t else 0)
      + (if wMon3 = d then 1 else 0) + (if wMon4 = d then wC t else 0)
      + (if wMon5 = d then wD t else 0) + (if wMon6 = d then wF t else 0) := by
  rw [wingerFamily_eq_monomials]
  simp [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_monomial]

theorem continuous_wA : Continuous wA := by
  unfold wA
  fun_prop

theorem continuous_wC : Continuous wC := by
  unfold wC
  fun_prop

theorem continuous_wD : Continuous wD := by
  unfold wD
  fun_prop

theorem continuous_wF : Continuous wF := by
  unfold wF
  fun_prop

theorem continuous_coeff_wingerFamily (d : Fin 3 →₀ ℕ) :
    Continuous (fun t : ℂ => (wingerFamily t).coeff d) := by
  have key : ∀ (b : Prop) [Decidable b] (f : ℂ → ℂ), Continuous f →
      Continuous (fun t : ℂ => if b then f t else 0) := by
    intro b _ f hf
    split_ifs with hb
    · exact hf
    · exact continuous_const
  simp only [coeff_wingerFamily d]
  have kA := key (wMon1 = d) wA continuous_wA
  have kB := key (wMon2 = d) wA continuous_wA
  have k1 := key (wMon3 = d) (fun _ : ℂ => (1 : ℂ)) continuous_const
  have kC := key (wMon4 = d) wC continuous_wC
  have kD := key (wMon5 = d) wD continuous_wD
  have kF := key (wMon6 = d) wF continuous_wF
  exact ((((kA.add kB).add k1).add kC).add kD).add kF

/-- The Winger family is continuous in the coefficientwise topology: each coefficient is
a polynomial in `t`. -/
theorem continuous_wingerFamily : Continuous (fun t : ℂ => wingerFamily t) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hnh : nhds (wingerFamily t₀) = Filter.comap (fun F d => F.coeff d)
      (nhds (fun d => (wingerFamily t₀).coeff d)) := nhds_induced _ _
  have htend : Filter.Tendsto (fun t : ℂ => wingerFamily t) (nhds t₀)
      (nhds (wingerFamily t₀)) := by
    rw [hnh, Filter.tendsto_comap_iff]
    rw [tendsto_pi_nhds]
    intro d
    exact (continuous_coeff_wingerFamily d).continuousAt
  exact htend

theorem wingerGood_one_div (n : ℕ) (hn : 0 < n) : WingerGood ((1 : ℂ) / (n : ℂ)) := by
  have hnc : ((n : ℂ)) ≠ 0 := by exact_mod_cast hn.ne'
  have hn2 : ((n : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 hnc
  have e1 : (3 : ℂ) * ((1 : ℂ) / (n : ℂ)) - 2 = (3 - 2 * (n : ℂ)) / (n : ℂ) := by
    field_simp
  have e2 : (3 : ℂ) * ((1 : ℂ) / (n : ℂ)) + 2 = (3 + 2 * (n : ℂ)) / (n : ℂ) := by
    field_simp
  have e3 : (4 : ℂ) * ((1 : ℂ) / (n : ℂ)) ^ 2 + 1
      = ((n : ℂ) ^ 2 + 4) / ((n : ℂ) ^ 2) := by
    field_simp
    ring
  have e4 : (9 : ℂ) * ((1 : ℂ) / (n : ℂ)) ^ 2 + 1
      = (9 + ((n : ℂ) ^ 2)) / ((n : ℂ) ^ 2) := by
    field_simp
  have hnum1 : (3 - 2 * (n : ℂ)) ≠ 0 := by
    intro h
    have h2 : (3 : ℕ) = 2 * n := by
      exact_mod_cast (by linear_combination h : (3 : ℂ) = 2 * (n : ℂ))
    omega
  have hnum2 : (3 + 2 * (n : ℂ)) ≠ 0 := by
    intro h
    have h2 : (3 : ℕ) + 2 * n = 0 := by
      exact_mod_cast (by linear_combination h : (3 : ℂ) + 2 * (n : ℂ) = 0)
    omega
  have hnum3 : ((n : ℂ) ^ 2 + 4) ≠ 0 := by
    have h : ((n : ℂ)) ^ 2 + 4 = ((n * n + 4 : ℕ)) := by
      push_cast
      ring
    rw [h]
    exact_mod_cast (by positivity : (n * n + 4 : ℕ) ≠ 0)
  have hnum4 : (9 + ((n : ℂ) ^ 2)) ≠ 0 := by
    have h : (9 : ℂ) + ((n : ℂ)) ^ 2 = ((9 + n * n : ℕ)) := by
      push_cast
      ring
    rw [h]
    exact_mod_cast (by positivity : (9 + n * n : ℕ) ≠ 0)
  refine ⟨div_ne_zero one_ne_zero hnc, ?_⟩
  have f1 : (3 : ℂ) * ((1 : ℂ) / (n : ℂ)) - 2 ≠ 0 := by
    rw [e1]
    exact div_ne_zero hnum1 hnc
  have f2 : (3 : ℂ) * ((1 : ℂ) / (n : ℂ)) + 2 ≠ 0 := by
    rw [e2]
    exact div_ne_zero hnum2 hnc
  have f3 : (4 : ℂ) * ((1 : ℂ) / (n : ℂ)) ^ 2 + 1 ≠ 0 := by
    rw [e3]
    exact div_ne_zero hnum3 hn2
  have f4 : (9 : ℂ) * ((1 : ℂ) / (n : ℂ)) ^ 2 + 1 ≠ 0 := by
    rw [e4]
    exact div_ne_zero hnum4 hn2
  intro h
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact f1 h
      · exact f2 h
    · exact f3 h
  · exact f4 h

/-- **The triple conic lies in the closure of the ten-nodal stratum.** The cube
`Q³ = (XY + Z²)³` of the smooth conic lies in the closure of `Σ_{10A_1}` in the
coefficientwise topology on ternary forms: the Winger degeneration is continuous
(`continuous_wingerFamily`), its value at `t = 0` is the triple conic
(`wingerFamily_zero`), and every parameter `t = 1 / n` with `n ≥ 1` is good
(`wingerGood_one_div`), where the family is ten-nodal
(`wingerFamily_mem_tenNodalStratum`). -/
theorem tripleConic_mem_closure_tenNodalStratum :
    (X 0 * X 1 + (X 2) ^ 2) ^ 3 ∈ closure TenNodalStratum := by
  rw [← wingerFamily_zero]
  refine mem_closure_of_tendsto (f := fun n : ℕ => wingerFamily ((1 : ℂ) / (n : ℂ)))
    (b := Filter.atTop) ?_ ?_
  · exact (continuous_wingerFamily.tendsto (0 : ℂ)).comp
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℂ))
  · refine (Filter.eventually_gt_atTop 0).mono ?_
    intro n hn
    exact wingerFamily_mem_tenNodalStratum _ (wingerGood_one_div n hn)

end LeanCategories.AlgebraicGeometry

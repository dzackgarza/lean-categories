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

@[expose] public section

/-!
# The triple conic lies in the closure of the ten-nodal sextic stratum

This file proves that the cube of the smooth conic `Q = (X * Y + Z ^ 2 = 0)` lies in the
Zariski closure, inside the projective space of ternary sextic forms `ℙ(Sym⁶ V^∨)` with
`V = ℂ³`, of the ten-nodal stratum `Σ_{10A_1}`: the set of nonzero sextic forms whose zero
locus in `ℙ²` has exactly ten singular points, each an ordinary node.

The degenerating family is the *Winger degeneration*
`H(t) = 27t³(X⁵Z + Y⁵Z) + X³Y³ + (729t⁶ + 18t² + 3)X²Y²Z² + (…)XYZ⁴ + (9t² + 1)⁵Z⁶`,
whose value at `t = 0` is the triple conic `(XY + Z²)³` and which, for every `t` avoiding
the finite set `{0, ±2/3, ±i/2, ±i/3}`, has exactly ten singular points, all ordinary nodes.

## Source

The Winger curve — the rational sextic with ten nodes whose degeneration to the triple conic
furnishes the family — appears in Dolgachev, *Corrado Segre and nodal cubic threefolds* (2018),
§7, pp. 13–14, via the parametrization `[u:v] ↦ [-v⁶ + 3u⁵v : u⁶ + 3uv⁵ : -5u³v³]`. The
translation of the closure question to the cube of a smooth conic is Yu–Zheng,
arXiv:1809.06589v2, Prop. 3.7, p. 10. The LC-09 search record for this file is in
`.scratch/lc09-145/results.txt`.

## Proof sketch

Each singular point of `V(H(t))` has `Z ≠ 0`; on the chart `Z = 1` the singular points
satisfy `x⁵ = y⁵` (Euler), so `x = ζy` with `ζ⁵ = 1`; writing `u = xy` one shows
`K(u) = u³ - cu² - 3du - 5f = 0` and `L(u) = g(u)² - 25a²u³ = 0` where `g(u) = 3u² + 2cu + d`.
Both `K` and `L` factor through the quadratic `q(u) = u² + (2 + 27t² - 729t⁶)u + (9t² + 1)⁴`,
whose two roots give, together with the five values of `ζ`, the ten singular points
`(ζy₀(u), y₀(u))` with `y₀ = -5aζ²u²/g(u)`. The Hessian minor at each of them is
`-5g(u)·(3u² - 2cu - 3d) ≠ 0`. Since the coefficient functions of `H` are polynomials in `t`
and the good set of `t` is cofinite, the standard one-variable polynomial argument shows every
homogeneous form vanishing on the stratum vanishes on the triple conic.
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
  rw [show ((n : ℕ) : MvPolynomial (Fin 3) ℂ) = C ((n : ℕ) : ℂ) from by simp [map_natCast], pderiv_C]

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

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.OrthogonalGroup
public import LeanCategories.Modules.Bilinear.Valued.TopologicalOrthogonalGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.Tactic

/-!
# The orthogonal group of a split binary lattice

Let `L` be a nondegenerate `ℤ`-lattice of rank two whose Gram matrix `G` has `-det G` a nonzero
square in `ℚ`. Equivalently `L ⊗ ℚ` is a hyperbolic plane: the binary form splits into two rational
isotropic lines. Then `SO(L)`, the kernel of `det : O(L) → ℤˣ`, is `{±1}`, and `O(L)` has at most
four elements. The bound is `[O(L) : SO(L)] ≤ 2` (`det` has its values in `ℤˣ`, a group of order
two) together with `|SO(L)| = 2`.

The proof is elementary. An isometry with determinant one either preserves each of the two
isotropic lines or swaps them. A swap is impossible: for isotropic `u`, `v` with `⟨u, v⟩ = k`
nonzero the form in the basis `(u, v)` is `k U`, and a map swapping the two lines multiplies it by
`-1`, so it cannot be an isometry of `k U` with determinant one. Hence `M` is `diag(λ, λ⁻¹)` in the
basis of the two lines, its trace `λ + λ⁻¹` is an integer, and a rational number whose sum with its
inverse is an integer is `±1`.

The orthogonal group here is the group `O(G) = {M ∈ GL₂(ℤ) : Mᵀ G M = G}` of the Gram matrix `G`,
which is how an isometry of a lattice presented by `G` appears; `specialMatrixOrthogonalGroup` is
its determinant-one subgroup, the image of `SO(L)`.

Search record (LC-09), through `scripts/formalization_corpus.py` over the whole index:
`BinaryQuadraticForm automorph`, `discriminant square isotropic binary form`, `hyperbolic plane
isometry group SL2`, `rational root monic integer polynomial`, `specialOrthogonal kernel det finite
index`, `TauCeti BinaryQuadraticForm Square`, `isotropic vector isotropic line binary form
rational`. The nearest hits are TauCeti `NumberTheory/BinaryQuadraticForm/{Root, Reduction}.lean`
(stabilizer orders for positive definite forms only) and `Split/Basic.lean` (isotropic vectors for
square discriminant, with no statement about automorphs); neither supplies this unit. In this
repository `orthogonalGroup_finite` (`Lattices/Valued/Mass.lean`) covered only positive definite
lattices, and the hyperbolic plane `hyperbolicPlane` (`Lattices/Valued/Standard.lean`) recorded
only its signature and indefiniteness.

Sources. C. O'Sullivan, *Topographs for binary quadratic forms and class numbers*,
arXiv:2408.14405v3, §8.1, Corollary 8.2 (p. 29): for a primitive form `q` of discriminant `D`,
`Aut(q) = {±I}` when `D` is a nonzero square or `D < -4`, where `Aut(q) ⊆ SL(2, ℤ)` and `Aut(λq) =
Aut(q)`. For a lattice with Gram matrix `G` the form is `q = [g₁₁, 2g₁₂, g₂₂]`, which has `D = -4
det G`, so the hypothesis `D` a nonzero square is `-det G` a nonzero square in `ℚ`. The index step
`[O(L) : SO(L)] ≤ 2` is elementary and is not stated in the source.
-/

@[expose] public section

namespace LeanCategories.Modules.Bilinear.Valued

open Matrix

/-! ## A rational number whose sum with its inverse is an integer -/

/-- A rational number whose sum with its inverse is an integer is `±1`. The rational root theorem
applied to the monic polynomial `X ^ 2 - k X + 1` makes the number an integer, and an integer whose
product with another integer is one is `±1`. -/
theorem rational_eq_one_or_neg_one_of_add_inv_eq_intCast {x : ℚ} (hx : x ≠ 0) {k : ℤ}
    (h : x + x⁻¹ = (k : ℚ)) : x = 1 ∨ x = -1 := by
  have hcast : x + x⁻¹ = algebraMap ℤ ℚ k := h
  have hpoly : x ^ 2 - algebraMap ℤ ℚ k * x + 1 = 0 := by
    have h1 := congrArg (· * x) hcast
    rw [add_mul, inv_mul_cancel₀ hx] at h1
    nlinarith [h1]
  have hint : IsIntegral ℤ x := by
    refine ⟨Polynomial.X ^ 2 + (-Polynomial.C k * Polynomial.X + 1), ?_, ?_⟩
    · refine Polynomial.monic_X_pow_add ?_
      compute_degree!
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_neg, Polynomial.eval₂_one, Polynomial.eval₂_X, Polynomial.eval₂_C]
      linarith
  obtain ⟨m, hm⟩ := UniqueFactorizationMonoid.integer_of_integral (A := ℤ) (K := ℚ) hint
  rw [← hm] at hpoly
  have hpb : ((m : ℚ)) ^ 2 - algebraMap ℤ ℚ k * (m : ℚ) + 1 = 0 := hpoly
  have hz : m * (m - k) = -1 := by
    have hq : (m : ℚ) * ((m : ℚ) - algebraMap ℤ ℚ k) = -1 := by nlinarith [hpb]
    have hq' : (m : ℚ) * ((m : ℚ) - (k : ℚ)) = -1 := hq
    exact_mod_cast hq'
  have hmul : (k - m) * m = 1 := by
    have h' : (k - m) * m = -(m * (m - k)) := by ring
    rw [h', hz]
    ring
  have hu : IsUnit m := ⟨⟨m, k - m, by rw [mul_comm]; exact hmul, hmul⟩, rfl⟩
  rcases Int.isUnit_iff.mp hu with h1 | h1
  · left; rw [← hm, h1]; norm_num
  · right; rw [← hm, h1]; norm_num

/-! ## The determinant character and the special orthogonal subgroup -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant of an isometry of a Gram matrix, as a unit of `ℤ`. -/
noncomputable def matrixOrthogonalDeterminant (B : Matrix n n ℤ) :
    MatrixOrthogonalGroup B →* ℤˣ :=
  (Matrix.GeneralLinearGroup.det).comp (MatrixOrthogonalGroup B).subtype

/-- `SO(B)`: the isometries of the Gram matrix `B` of determinant one. -/
noncomputable def specialMatrixOrthogonalGroup (B : Matrix n n ℤ) :
    Subgroup (MatrixOrthogonalGroup B) :=
  MonoidHom.ker (matrixOrthogonalDeterminant B)

@[simp]
theorem coe_matrixOrthogonalDeterminant (B : Matrix n n ℤ) (g : MatrixOrthogonalGroup B) :
    ((matrixOrthogonalDeterminant B g : ℤˣ) : ℤ) =
      ((g : Matrix.GeneralLinearGroup n ℤ) : Matrix n n ℤ).det :=
  rfl

theorem mem_specialMatrixOrthogonalGroup {B : Matrix n n ℤ} {g : MatrixOrthogonalGroup B} :
    g ∈ specialMatrixOrthogonalGroup B ↔
      ((g : Matrix.GeneralLinearGroup n ℤ) : Matrix n n ℤ).det = 1 := by
  rw [specialMatrixOrthogonalGroup, MonoidHom.mem_ker]
  constructor
  · intro h
    simpa using congrArg Units.val h
  · intro h
    refine Units.ext ?_
    simpa using h

/-- `SO(B)` has index at most two in `O(B)`: `det` maps into the group `ℤˣ` of order two. -/
theorem specialMatrixOrthogonalGroup_index_le_two (B : Matrix n n ℤ) :
    (specialMatrixOrthogonalGroup B).index ≤ 2 := by
  rw [specialMatrixOrthogonalGroup, Subgroup.index_ker]
  calc Nat.card ↥(MonoidHom.range (matrixOrthogonalDeterminant B))
      ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]

/-! ## The hyperbolic normal form of a split binary form -/

/-- The Gram matrix of the hyperbolic plane over `ℚ`. -/
def splitPairMatrix : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]

/-- A rational coordinate change putting a split binary form in hyperbolic normal form: a matrix of
nonzero determinant and a nonzero scalar `k` with `Pᵀ (!![a, b; b, c]) P = k • U`. The columns
of `P` are two isotropic vectors pairing to `k`. -/
theorem exists_split_basis {a b c σ : ℚ} (hσ : σ ≠ 0) (hsq : σ ^ 2 = b ^ 2 - a * c)
    (hdet : a * c - b * b ≠ 0) :
    ∃ (P : Matrix (Fin 2) (Fin 2) ℚ) (k : ℚ), P.det ≠ 0 ∧ k ≠ 0 ∧
      Pᵀ * !![a, b; b, c] * P = k • splitPairMatrix := by
  have hkey : σ ^ 2 - b ^ 2 + a * c = 0 := by linarith
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by
      intro hb0
      exact hdet (by rw [hb0]; ring)
    refine ⟨!![1, -c; 0, 2 * b], 2 * b ^ 2, ?_, mul_ne_zero two_ne_zero (pow_ne_zero 2 hb), ?_⟩
    · rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      have h1 : (1 : ℚ) * (2 * b) - -c * 0 = 2 * b := by ring
      rw [h1]
      exact mul_ne_zero two_ne_zero hb
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [splitPairMatrix, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two]
      all_goals ring
  · refine ⟨!![σ - b, -b - σ; a, a], 2 * a * (a * c - b * b), ?_,
      mul_ne_zero (mul_ne_zero two_ne_zero ha) hdet, ?_⟩
    · rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      have h1 : (σ - b) * a - (-b - σ) * a = 2 * a * σ := by ring
      rw [h1]
      exact mul_ne_zero (mul_ne_zero two_ne_zero ha) hσ
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [splitPairMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination a * hkey
      · linear_combination -a * hkey
      · linear_combination -a * hkey
      · linear_combination a * hkey

/-! ## A rational isometry of the hyperbolic plane with integral trace -/

/-- A rational isometry of the hyperbolic plane of determinant one and integral trace is `±1`. -/
theorem eq_pm_one_of_hyperbolic_isometry {N : Matrix (Fin 2) (Fin 2) ℚ}
    (hN : Nᵀ * splitPairMatrix * N = splitPairMatrix) (hdet : N.det = 1) {t : ℤ}
    (htr : N.trace = (t : ℚ)) : N = 1 ∨ N = -1 := by
  have h00 : N 0 0 * N 1 0 = 0 := by
    have h := congrFun (congrFun hN 0) 0
    norm_num [splitPairMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h
    linarith
  have h11 : N 0 1 * N 1 1 = 0 := by
    have h := congrFun (congrFun hN 1) 1
    norm_num [splitPairMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h
    linarith
  have h01 : N 0 0 * N 1 1 + N 1 0 * N 0 1 = 1 := by
    have h := congrFun (congrFun hN 0) 1
    norm_num [splitPairMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h
    linarith
  have hdet' : N 0 0 * N 1 1 - N 0 1 * N 1 0 = 1 := by
    rw [← hdet, Matrix.det_fin_two]
  have hps : N 0 0 * N 1 1 = 1 := by linarith
  have hqr : N 0 1 * N 1 0 = 0 := by linarith
  have hp : N 0 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hps
    exact zero_ne_one hps
  have hs : N 1 1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hps
    exact zero_ne_one hps
  have hr : N 1 0 = 0 := (mul_eq_zero.mp h00).resolve_left hp
  have hq : N 0 1 = 0 := (mul_eq_zero.mp h11).resolve_right hs
  have hs_eq : N 1 1 = (N 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hps
  have htr' : N 0 0 + (N 0 0)⁻¹ = (t : ℚ) := by
    rw [← htr, Matrix.trace_fin_two, hs_eq]
  rcases rational_eq_one_or_neg_one_of_add_inv_eq_intCast hp htr' with h | h
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h, hr, hq, hs_eq]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h, hr, hq, hs_eq]

/-! ## Conjugation of an isometry -/

/-- Conjugating an isometry of `A` by an invertible `P` is an isometry of `Pᵀ A P`. -/
theorem conjugate_isometry {A M P : Matrix (Fin 2) (Fin 2) ℚ} [Invertible P]
    (hM : Mᵀ * A * M = A) :
    (P⁻¹ * M * P)ᵀ * (Pᵀ * A * P) * (P⁻¹ * M * P) = Pᵀ * A * P := by
  have hPP : P * P⁻¹ = 1 := Matrix.mul_inv_of_invertible P
  have hT : (P⁻¹)ᵀ * Pᵀ = 1 := by
    rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
  calc (P⁻¹ * M * P)ᵀ * (Pᵀ * A * P) * (P⁻¹ * M * P)
      = Pᵀ * Mᵀ * ((P⁻¹)ᵀ * Pᵀ) * A * (P * P⁻¹) * M * P := by
        simp only [Matrix.transpose_mul]
        noncomm_ring
    _ = Pᵀ * Mᵀ * 1 * A * 1 * M * P := by rw [hT, hPP]
    _ = Pᵀ * (Mᵀ * A * M) * P := by noncomm_ring
    _ = Pᵀ * A * P := by rw [hM]

/-! ## The special orthogonal group of a split binary lattice -/

/-- **Every determinant-one isometry of a nondegenerate split binary lattice is `±1`.** -/
theorem isometry_eq_pm_one_of_neg_det_isSquare {a b c : ℤ}
    (hdet : a * c - b * b ≠ 0)
    (hsq : ∃ σ : ℚ, σ ≠ 0 ∧ ((a : ℚ) * c - (b : ℚ) * b) = -σ ^ 2)
    (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hiso : Mᵀ * !![a, b; b, c] * M = !![a, b; b, c]) (hdetM : M.det = 1) :
    M = 1 ∨ M = -1 := by
  classical
  obtain ⟨σ, hσ, hσsq⟩ := hsq
  have hsq' : σ ^ 2 = (b : ℚ) ^ 2 - (a : ℚ) * (c : ℚ) := by linarith
  have hdet' : (a : ℚ) * c - (b : ℚ) * b ≠ 0 := by
    intro h
    exact hdet (by exact_mod_cast h)
  obtain ⟨P, k, hPdet, hk, hPAP⟩ := exists_split_basis hσ hsq' hdet'
  haveI : Invertible P := Matrix.invertibleOfIsUnitDet P (isUnit_iff_ne_zero.mpr hPdet)
  let G : Matrix (Fin 2) (Fin 2) ℤ := !![a, b; b, c]
  let A : Matrix (Fin 2) (Fin 2) ℚ := !![(a : ℚ), (b : ℚ); (b : ℚ), (c : ℚ)]
  let Mq : Matrix (Fin 2) (Fin 2) ℚ := M.map (Int.castRingHom ℚ)
  have hisoG : Mᵀ * G * M = G := hiso
  have hGA : G.map (Int.castRingHom ℚ) = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [G, A, Matrix.map_apply]
  have hisoQ : Mqᵀ * A * Mq = A := by
    have h := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℤ => X.map (Int.castRingHom ℚ)) hisoG
    rw [← hGA]
    simpa only [Mq, Matrix.map_mul, Matrix.transpose_map] using h
  have hdetMq : Mq.det = 1 := by
    have h := RingHom.map_det (Int.castRingHom ℚ) M
    rw [hdetM] at h
    have h' : (Int.castRingHom ℚ).mapMatrix M = Mq := by
      ext i j
      simp [Mq, RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [h', map_one] at h
    exact h.symm
  have hNH : (P⁻¹ * Mq * P)ᵀ * splitPairMatrix * (P⁻¹ * Mq * P) = splitPairMatrix := by
    have hH : splitPairMatrix = k⁻¹ • (Pᵀ * A * P) := by
      rw [hPAP, smul_smul, inv_mul_cancel₀ hk, one_smul]
    have hkey := conjugate_isometry (A := A) (M := Mq) (P := P) hisoQ
    calc (P⁻¹ * Mq * P)ᵀ * splitPairMatrix * (P⁻¹ * Mq * P)
        = (P⁻¹ * Mq * P)ᵀ * (k⁻¹ • (Pᵀ * A * P)) * (P⁻¹ * Mq * P) := by rw [hH]
      _ = k⁻¹ • ((P⁻¹ * Mq * P)ᵀ * (Pᵀ * A * P) * (P⁻¹ * Mq * P)) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = k⁻¹ • (Pᵀ * A * P) := by rw [hkey]
      _ = splitPairMatrix := by rw [← hH]
  have hNdet : (P⁻¹ * Mq * P).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hdetMq, mul_one, ← Matrix.det_mul,
      Matrix.inv_mul_of_invertible, Matrix.det_one]
  have htrN : (P⁻¹ * Mq * P).trace = ((M.trace : ℤ) : ℚ) := by
    have hPP : P * P⁻¹ = 1 := Matrix.mul_inv_of_invertible P
    calc (P⁻¹ * Mq * P).trace = (P⁻¹ * (Mq * P)).trace := by rw [Matrix.mul_assoc]
      _ = ((Mq * P) * P⁻¹).trace := Matrix.trace_mul_comm _ _
      _ = (Mq * (P * P⁻¹)).trace := by rw [Matrix.mul_assoc]
      _ = Mq.trace := by rw [hPP, Matrix.mul_one]
      _ = ((M.trace : ℤ) : ℚ) := by
          simp only [Mq, Matrix.trace, Matrix.diag_apply, Matrix.map_apply, Fin.sum_univ_two,
            Int.coe_castRingHom]
          push_cast
          ring
  have hconj : P * (P⁻¹ * Mq * P) * P⁻¹ = Mq := by
    have hPP : P * P⁻¹ = 1 := Matrix.mul_inv_of_invertible P
    calc P * (P⁻¹ * Mq * P) * P⁻¹ = (P * P⁻¹) * Mq * (P * P⁻¹) := by noncomm_ring
      _ = Mq := by rw [hPP]; noncomm_ring
  rcases eq_pm_one_of_hyperbolic_isometry hNH hNdet htrN with hN | hN
  · left
    have hMq : Mq = 1 := by
      rw [← hconj, hN, Matrix.mul_one, Matrix.mul_inv_of_invertible]
    ext i j
    have h := congrFun (congrFun hMq i) j
    simp only [Mq, Matrix.map_apply, Matrix.one_apply] at h
    have h2 : ((M i j : ℤ) : ℚ) = (((1 : Matrix (Fin 2) (Fin 2) ℤ)) i j : ℚ) := by
      simpa [Matrix.one_apply] using h
    exact_mod_cast h2
  · right
    have hMq : Mq = -1 := by
      rw [← hconj, hN, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
        Matrix.mul_inv_of_invertible]
    ext i j
    have h := congrFun (congrFun hMq i) j
    simp only [Mq, Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply] at h
    have h2 : ((M i j : ℤ) : ℚ) =
        (((-1 : Matrix (Fin 2) (Fin 2) ℤ)) i j : ℚ) := by
      simpa [Matrix.neg_apply, Matrix.one_apply] using h
    exact_mod_cast h2

/-- The special orthogonal group of a split binary lattice is `{±1}`. -/
theorem specialMatrixOrthogonalGroup_eq_pm_one {a b c : ℤ}
    (hdet : a * c - b * b ≠ 0)
    (hsq : ∃ σ : ℚ, σ ≠ 0 ∧ ((a : ℚ) * c - (b : ℚ) * b) = -σ ^ 2)
    {g : MatrixOrthogonalGroup (!![a, b; b, c])}
    (hg : g ∈ specialMatrixOrthogonalGroup (!![a, b; b, c])) :
    (((g : MatrixOrthogonalGroup (!![a, b; b, c])) : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) = 1 ∨
      (((g : MatrixOrthogonalGroup (!![a, b; b, c])) : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) = -1 :=
  isometry_eq_pm_one_of_neg_det_isSquare hdet hsq _ g.2
    (mem_specialMatrixOrthogonalGroup.mp hg)

/-- An injection of the special orthogonal group of a split binary Gram matrix into `Fin 2`: by
`specialMatrixOrthogonalGroup_eq_pm_one` its elements are `1` and `-1`. -/
theorem exists_injective_specialMatrixOrthogonalGroup_fin_two {a b c : ℤ}
    (hdet : a * c - b * b ≠ 0)
    (hsq : ∃ σ : ℚ, σ ≠ 0 ∧ ((a : ℚ) * c - (b : ℚ) * b) = -σ ^ 2) :
    ∃ f : specialMatrixOrthogonalGroup (!![a, b; b, c]) → Fin 2, Function.Injective f := by
  classical
  have hneg : (-1 : Matrix (Fin 2) (Fin 2) ℤ) ≠ 1 := by
    intro h
    have h00 := congrFun (congrFun h 0) 0
    norm_num at h00
  have hm : ∀ g : specialMatrixOrthogonalGroup (!![a, b; b, c]),
      (((g : MatrixOrthogonalGroup (!![a, b; b, c])) : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
          Matrix (Fin 2) (Fin 2) ℤ) = 1 ∨
        (((g : MatrixOrthogonalGroup (!![a, b; b, c])) : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
          Matrix (Fin 2) (Fin 2) ℤ) = -1 :=
    fun g => specialMatrixOrthogonalGroup_eq_pm_one hdet hsq g.2
  let f : specialMatrixOrthogonalGroup (!![a, b; b, c]) → Fin 2 := fun g =>
    if (((g : MatrixOrthogonalGroup (!![a, b; b, c])) : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) = 1 then 0 else 1
  refine ⟨f, ?_⟩
  intro g h hgh
  have hg' := hm g
  have hh' := hm h
  simp only [f] at hgh
  rcases hg' with hg' | hg' <;> rcases hh' with hh' | hh'
  · exact Subtype.ext (Subtype.ext (Units.ext (hg'.trans hh'.symm)))
  · exfalso
    rw [if_pos hg'] at hgh
    have hne : ¬ ((((h : MatrixOrthogonalGroup (!![a, b; b, c])) :
        Matrix.GeneralLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = 1) := by
      rw [hh']
      exact hneg
    rw [if_neg hne] at hgh
    exact absurd hgh (by decide)
  · exfalso
    have hne : ¬ ((((g : MatrixOrthogonalGroup (!![a, b; b, c])) :
        Matrix.GeneralLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = 1) := by
      rw [hg']
      exact hneg
    rw [if_neg hne, if_pos hh'] at hgh
    exact absurd hgh (by decide)
  · exact Subtype.ext (Subtype.ext (Units.ext (hg'.trans hh'.symm)))

/-- The special orthogonal group of a split binary lattice has at most two elements. -/
theorem natCard_specialMatrixOrthogonalGroup_le_two {a b c : ℤ}
    (hdet : a * c - b * b ≠ 0)
    (hsq : ∃ σ : ℚ, σ ≠ 0 ∧ ((a : ℚ) * c - (b : ℚ) * b) = -σ ^ 2) :
    Nat.card (specialMatrixOrthogonalGroup (!![a, b; b, c])) ≤ 2 := by
  obtain ⟨f, hf⟩ := exists_injective_specialMatrixOrthogonalGroup_fin_two hdet hsq
  have h2 : Nat.card (Fin 2) = 2 := by simp
  have h3 := Nat.card_le_card_of_injective f hf
  omega

/-- The orthogonal group of a split binary lattice is finite. -/
theorem finite_matrixOrthogonalGroup {a b c : ℤ}
    (hdet : a * c - b * b ≠ 0)
    (hsq : ∃ σ : ℚ, σ ≠ 0 ∧ ((a : ℚ) * c - (b : ℚ) * b) = -σ ^ 2) :
    Finite (MatrixOrthogonalGroup (!![a, b; b, c])) := by
  classical
  obtain ⟨f, hf⟩ := exists_injective_specialMatrixOrthogonalGroup_fin_two hdet hsq
  have hfinSO : Finite (specialMatrixOrthogonalGroup (!![a, b; b, c])) :=
    Finite.of_injective f hf
  have hneSO : Nat.card (specialMatrixOrthogonalGroup (!![a, b; b, c])) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, hfinSO⟩
  have hfinRange : Finite (MonoidHom.range
      (matrixOrthogonalDeterminant (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℤ))) :=
    Finite.of_injective _ Subtype.val_injective
  have hneIdx : (specialMatrixOrthogonalGroup (!![a, b; b, c])).index ≠ 0 := by
    rw [specialMatrixOrthogonalGroup, Subgroup.index_ker]
    exact Nat.card_ne_zero.mpr
      ⟨⟨1, MonoidHom.mem_range.mpr ⟨1, map_one _⟩⟩, hfinRange⟩
  have hcard := Subgroup.card_mul_index (specialMatrixOrthogonalGroup (!![a, b; b, c]))
  have hne : Nat.card (MatrixOrthogonalGroup (!![a, b; b, c])) ≠ 0 := by
    rw [← hcard]
    exact Nat.mul_ne_zero hneSO hneIdx
  exact (Nat.card_ne_zero.mp hne).2

/-- The orthogonal group of a split binary lattice has at most four elements: `SO` has two and
`[O : SO] ≤ 2`.
-/
theorem natCard_matrixOrthogonalGroup_le_four {a b c : ℤ}
    (hdet : a * c - b * b ≠ 0)
    (hsq : ∃ σ : ℚ, σ ≠ 0 ∧ ((a : ℚ) * c - (b : ℚ) * b) = -σ ^ 2) :
    Nat.card (MatrixOrthogonalGroup (!![a, b; b, c])) ≤ 4 := by
  have hSO := natCard_specialMatrixOrthogonalGroup_le_two hdet hsq
  have hcard := Subgroup.card_mul_index (specialMatrixOrthogonalGroup (!![a, b; b, c]))
  have hidx := specialMatrixOrthogonalGroup_index_le_two
    (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℤ)
  rw [← hcard]
  calc Nat.card (specialMatrixOrthogonalGroup (!![a, b; b, c])) *
        (specialMatrixOrthogonalGroup (!![a, b; b, c])).index ≤ 2 * 2 :=
        Nat.mul_le_mul hSO hidx
    _ = 4 := by norm_num


/-! ## The hyperbolic plane -/

/-- The Gram matrix of the integral hyperbolic plane. -/
abbrev hyperbolicPairMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- The underlying matrix of an element of the orthogonal group of a Gram matrix. -/
abbrev orthoMatrix (B : Matrix n n ℤ) (g : MatrixOrthogonalGroup B) : Matrix n n ℤ :=
  ((g : Matrix.GeneralLinearGroup n ℤ) : Matrix n n ℤ)

theorem orthoMatrix_injective (B : Matrix n n ℤ) : Function.Injective (orthoMatrix B) :=
  fun _ _ hgh => Subtype.ext (Units.ext hgh)

theorem orthoMatrix_mul (B : Matrix n n ℤ) (g h : MatrixOrthogonalGroup B) :
    orthoMatrix B (g * h) = orthoMatrix B g * orthoMatrix B h :=
  rfl

theorem hyperbolicPairMatrix_det : hyperbolicPairMatrix.det = -1 := by
  rw [hyperbolicPairMatrix, Matrix.det_fin_two]
  norm_num

theorem hyperbolicPairMatrix_transpose : hyperbolicPairMatrixᵀ = hyperbolicPairMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [hyperbolicPairMatrix]

theorem hyperbolicPairMatrix_mul_self : hyperbolicPairMatrix * hyperbolicPairMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hyperbolicPairMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The swap `U` as an isometry of the hyperbolic plane, of determinant `-1`. -/
def hyperbolicSwap : MatrixOrthogonalGroup hyperbolicPairMatrix :=
  ⟨⟨hyperbolicPairMatrix, hyperbolicPairMatrix, hyperbolicPairMatrix_mul_self,
      hyperbolicPairMatrix_mul_self⟩, by
    change hyperbolicPairMatrix.transpose * hyperbolicPairMatrix * hyperbolicPairMatrix =
      hyperbolicPairMatrix
    rw [hyperbolicPairMatrix_transpose, hyperbolicPairMatrix_mul_self, Matrix.one_mul]⟩

/-- `-U` as an isometry of the hyperbolic plane. -/
def hyperbolicNegSwap : MatrixOrthogonalGroup hyperbolicPairMatrix :=
  ⟨⟨-hyperbolicPairMatrix, -hyperbolicPairMatrix,
      by rw [neg_mul_neg, hyperbolicPairMatrix_mul_self],
      by rw [neg_mul_neg, hyperbolicPairMatrix_mul_self]⟩, by
    change (-hyperbolicPairMatrix).transpose * hyperbolicPairMatrix * (-hyperbolicPairMatrix) =
      hyperbolicPairMatrix
    rw [Matrix.transpose_neg, hyperbolicPairMatrix_transpose, Matrix.neg_mul,
      hyperbolicPairMatrix_mul_self, Matrix.neg_mul, Matrix.one_mul, neg_neg]⟩

/-- `-1` as an isometry of the hyperbolic plane. -/
def hyperbolicNegOne : MatrixOrthogonalGroup hyperbolicPairMatrix :=
  ⟨⟨-1, -1, by rw [neg_mul_neg, Matrix.one_mul],
      by rw [neg_mul_neg, Matrix.one_mul]⟩, by
    change (-1 : Matrix (Fin 2) (Fin 2) ℤ).transpose * hyperbolicPairMatrix * (-1) =
      hyperbolicPairMatrix
    rw [Matrix.transpose_neg, Matrix.transpose_one, Matrix.neg_mul, Matrix.one_mul,
      Matrix.mul_neg, Matrix.mul_one, neg_neg]⟩

@[simp]
theorem orthoMatrix_hyperbolicSwap :
    orthoMatrix hyperbolicPairMatrix hyperbolicSwap = hyperbolicPairMatrix :=
  rfl

@[simp]
theorem orthoMatrix_hyperbolicNegOne :
    orthoMatrix hyperbolicPairMatrix hyperbolicNegOne = -1 :=
  rfl

@[simp]
theorem orthoMatrix_hyperbolicNegSwap :
    orthoMatrix hyperbolicPairMatrix hyperbolicNegSwap = -hyperbolicPairMatrix :=
  rfl

theorem hyperbolicPairMatrix_det_ne_zero : (0 : ℤ) * 0 - 1 * 1 ≠ 0 := by norm_num

theorem hyperbolicPairMatrix_sq :
    ∃ σ : ℚ, σ ≠ 0 ∧ ((0 : ℚ) * 0 - (1 : ℚ) * 1) = -σ ^ 2 :=
  ⟨1, one_ne_zero, by norm_num⟩

/-- **`O(U) = {±1, ±U}`**: every isometry of the integral hyperbolic plane is the identity, minus
the identity, the swap `U = !![0, 1; 1, 0]`, or minus the swap. -/
theorem matrixOrthogonalGroup_hyperbolicPair {M : MatrixOrthogonalGroup hyperbolicPairMatrix} :
    orthoMatrix hyperbolicPairMatrix M = 1 ∨ orthoMatrix hyperbolicPairMatrix M = -1 ∨
      orthoMatrix hyperbolicPairMatrix M = hyperbolicPairMatrix ∨
        orthoMatrix hyperbolicPairMatrix M = -hyperbolicPairMatrix := by
  have hval := coe_matrixOrthogonalDeterminant hyperbolicPairMatrix M
  rcases Int.units_eq_one_or (matrixOrthogonalDeterminant hyperbolicPairMatrix M) with hu | hu
  · have hdet : (orthoMatrix hyperbolicPairMatrix M).det = 1 := by
      rw [← hval, hu]
      norm_num
    rcases specialMatrixOrthogonalGroup_eq_pm_one hyperbolicPairMatrix_det_ne_zero
      hyperbolicPairMatrix_sq (by
        rw [mem_specialMatrixOrthogonalGroup]
        exact hdet) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hdet : (orthoMatrix hyperbolicPairMatrix M).det = -1 := by
      rw [← hval, hu]
      norm_num
    have hJM : hyperbolicSwap * M ∈ specialMatrixOrthogonalGroup hyperbolicPairMatrix := by
      rw [mem_specialMatrixOrthogonalGroup]
      change (orthoMatrix hyperbolicPairMatrix (hyperbolicSwap * M)).det = 1
      rw [orthoMatrix_mul, Matrix.det_mul, orthoMatrix_hyperbolicSwap, hyperbolicPairMatrix_det,
        hdet]
      norm_num
    rcases specialMatrixOrthogonalGroup_eq_pm_one hyperbolicPairMatrix_det_ne_zero
      hyperbolicPairMatrix_sq hJM with h | h
    · right; right; left
      have hh : hyperbolicPairMatrix * orthoMatrix hyperbolicPairMatrix M = 1 := by
        have h' : orthoMatrix hyperbolicPairMatrix (hyperbolicSwap * M) = 1 := h
        rwa [orthoMatrix_mul, orthoMatrix_hyperbolicSwap] at h'
      calc orthoMatrix hyperbolicPairMatrix M
          = hyperbolicPairMatrix *
              (hyperbolicPairMatrix * orthoMatrix hyperbolicPairMatrix M) := by
            rw [← Matrix.mul_assoc, hyperbolicPairMatrix_mul_self, Matrix.one_mul]
        _ = hyperbolicPairMatrix * 1 := by rw [hh]
        _ = hyperbolicPairMatrix := Matrix.mul_one _
    · right; right; right
      have hh : hyperbolicPairMatrix * orthoMatrix hyperbolicPairMatrix M = -1 := by
        have h' : orthoMatrix hyperbolicPairMatrix (hyperbolicSwap * M) = -1 := h
        rwa [orthoMatrix_mul, orthoMatrix_hyperbolicSwap] at h'
      calc orthoMatrix hyperbolicPairMatrix M
          = hyperbolicPairMatrix *
              (hyperbolicPairMatrix * orthoMatrix hyperbolicPairMatrix M) := by
            rw [← Matrix.mul_assoc, hyperbolicPairMatrix_mul_self, Matrix.one_mul]
        _ = hyperbolicPairMatrix * (-1) := by rw [hh]
        _ = -hyperbolicPairMatrix := by rw [Matrix.mul_neg, Matrix.mul_one]

/-- The four isometries `1`, `-1`, `U`, `-U` of the hyperbolic plane are distinct. -/
theorem injective_hyperbolic_isometries :
    Function.Injective fun i : Fin 4 =>
      match i with
      | 0 => (1 : MatrixOrthogonalGroup hyperbolicPairMatrix)
      | 1 => hyperbolicNegOne
      | 2 => hyperbolicSwap
      | 3 => hyperbolicNegSwap := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (exfalso
       exact absurd (congrArg (orthoMatrix hyperbolicPairMatrix) h) (by decide))

/-- The orthogonal group of the hyperbolic plane has exactly four elements. -/
theorem natCard_matrixOrthogonalGroup_hyperbolicPair :
    Nat.card (MatrixOrthogonalGroup hyperbolicPairMatrix) = 4 := by
  haveI hfin : Finite (MatrixOrthogonalGroup hyperbolicPairMatrix) :=
    finite_matrixOrthogonalGroup hyperbolicPairMatrix_det_ne_zero hyperbolicPairMatrix_sq
  have h4 : Nat.card (Fin 4) = 4 := by simp
  have hge : 4 ≤ Nat.card (MatrixOrthogonalGroup hyperbolicPairMatrix) := by
    have := Nat.card_le_card_of_injective _ injective_hyperbolic_isometries
    omega
  have hle : Nat.card (MatrixOrthogonalGroup hyperbolicPairMatrix) ≤ 4 :=
    natCard_matrixOrthogonalGroup_le_four hyperbolicPairMatrix_det_ne_zero hyperbolicPairMatrix_sq
  omega


/-! ## The matrix theorem for an arbitrary symmetric binary Gram matrix -/

theorem matrix_eq_of_transpose_eq {G : Matrix (Fin 2) (Fin 2) ℤ} (hsymm : Gᵀ = G) :
    G = !![G 0 0, G 0 1; G 0 1, G 1 1] := by
  have h10 : G 1 0 = G 0 1 := by
    have h := congrFun (congrFun hsymm 1) 0
    simpa using h.symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10]

theorem isometry_eq_pm_one_of_neg_det_isSquare_of_symm {G : Matrix (Fin 2) (Fin 2) ℤ}
    (hsymm : Gᵀ = G) (hdet : G.det ≠ 0)
    (hsq : ∃ σ : ℚ, σ ≠ 0 ∧ (G.det : ℚ) = -σ ^ 2)
    {M : Matrix (Fin 2) (Fin 2) ℤ} (hiso : Mᵀ * G * M = G) (hdetM : M.det = 1) :
    M = 1 ∨ M = -1 := by
  have hG := matrix_eq_of_transpose_eq hsymm
  rw [hG] at hdet hsq hiso
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨σ, hσ, hsqσ⟩ := hsq
  have hsq' : (G 0 0 : ℚ) * (G 1 1) - (G 0 1 : ℚ) * (G 0 1) = -σ ^ 2 := by
    rw [Matrix.det_fin_two] at hsqσ
    simpa using hsqσ
  exact isometry_eq_pm_one_of_neg_det_isSquare (a := G 0 0) (b := G 0 1) (c := G 1 1)
    hdet ⟨σ, hσ, hsq'⟩ M hiso hdetM

theorem finite_matrixOrthogonalGroup_of_symm {G : Matrix (Fin 2) (Fin 2) ℤ}
    (hsymm : Gᵀ = G) (hdet : G.det ≠ 0)
    (hsq : ∃ σ : ℚ, σ ≠ 0 ∧ (G.det : ℚ) = -σ ^ 2) :
    Finite (MatrixOrthogonalGroup G) := by
  have hG := matrix_eq_of_transpose_eq hsymm
  rw [hG] at hdet hsq ⊢
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨σ, hσ, hsqσ⟩ := hsq
  have hsq' : (G 0 0 : ℚ) * (G 1 1) - (G 0 1 : ℚ) * (G 0 1) = -σ ^ 2 := by
    rw [Matrix.det_fin_two] at hsqσ
    simpa using hsqσ
  exact finite_matrixOrthogonalGroup (a := G 0 0) (b := G 0 1) (c := G 1 1) hdet
    ⟨σ, hσ, hsq'⟩

theorem natCard_matrixOrthogonalGroup_le_four_of_symm {G : Matrix (Fin 2) (Fin 2) ℤ}
    (hsymm : Gᵀ = G) (hdet : G.det ≠ 0)
    (hsq : ∃ σ : ℚ, σ ≠ 0 ∧ (G.det : ℚ) = -σ ^ 2) :
    Nat.card (MatrixOrthogonalGroup G) ≤ 4 := by
  have hG := matrix_eq_of_transpose_eq hsymm
  rw [hG] at hdet hsq ⊢
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨σ, hσ, hsqσ⟩ := hsq
  have hsq' : (G 0 0 : ℚ) * (G 1 1) - (G 0 1 : ℚ) * (G 0 1) = -σ ^ 2 := by
    rw [Matrix.det_fin_two] at hsqσ
    simpa using hsqσ
  exact natCard_matrixOrthogonalGroup_le_four (a := G 0 0) (b := G 0 1) (c := G 1 1) hdet
    ⟨σ, hσ, hsq'⟩

end LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

open Matrix
open LeanCategories.Modules.Bilinear.Valued

/-! ## The split binary lattice -/

/-- The matrix of an isometry of a lattice in a basis. -/
noncomputable def isometryMatrix (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis (Fin 2) ℤ L.obj.obj.carrier) (g : OrthogonalGroup L.obj) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  LinearMap.toMatrix b b (g.1 : L.obj.obj.carrier →ₗ[ℤ] L.obj.obj.carrier)

theorem linearMap_eq_of_toMatrix_eq {M : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis (Fin 2) ℤ M) {f h : M →ₗ[ℤ] M}
    (hfh : LinearMap.toMatrix b b f = LinearMap.toMatrix b b h) : f = h := by
  refine b.ext fun j => b.equivFun.injective ?_
  funext i
  have h := congrFun (congrFun hfh i) j
  simpa [LinearMap.toMatrix_apply, Module.Basis.equivFun_apply] using h

theorem isometryMatrix_injective (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis (Fin 2) ℤ L.obj.obj.carrier) :
    Function.Injective (isometryMatrix L b) := by
  intro g h hgh
  refine Subtype.ext (LinearEquiv.toLinearMap_injective ?_)
  exact linearMap_eq_of_toMatrix_eq b hgh

/-- The Gram matrix of a lattice basis is symmetric. -/
theorem gramMatrix_transpose (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis (Fin 2) ℤ L.obj.obj.carrier) :
    (gramMatrix L.obj b)ᵀ = gramMatrix L.obj b := by
  ext i j
  simp only [Matrix.transpose_apply, gramMatrix, LinearMap.BilinForm.toMatrix_apply,
    BilinModuleCat.bilinMap_apply]
  exact L.obj.property.2 (b j) (b i)

/-- An isometry of a lattice is an isometry of its Gram matrix in any basis. -/
theorem isometryMatrix_gram (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis (Fin 2) ℤ L.obj.obj.carrier) (g : OrthogonalGroup L.obj) :
    (isometryMatrix L b g)ᵀ * gramMatrix L.obj b * isometryMatrix L b g =
      gramMatrix L.obj b := by
  have hcomp : LinearMap.BilinForm.comp L.obj.obj.bilinMap g.1.toLinearMap g.1.toLinearMap =
      L.obj.obj.bilinMap := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simpa using g.2 x y
  have h := LinearMap.BilinForm.toMatrix_comp (b := b) (c := b) (B := L.obj.obj.bilinMap)
    (l := g.1.toLinearMap) (r := g.1.toLinearMap)
  rw [hcomp] at h
  exact h.symm

theorem isometryMatrix_det_mul_self (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis (Fin 2) ℤ L.obj.obj.carrier) (g : OrthogonalGroup L.obj)
    (hdet : (gramMatrix L.obj b).det ≠ 0) :
    (isometryMatrix L b g).det * (isometryMatrix L b g).det = 1 := by
  have h := congrArg Matrix.det (isometryMatrix_gram L b g)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  refine mul_right_cancel₀ hdet ?_
  linear_combination h

theorem isometryMatrix_isUnit_det (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis (Fin 2) ℤ L.obj.obj.carrier) (g : OrthogonalGroup L.obj)
    (hdet : (gramMatrix L.obj b).det ≠ 0) :
    IsUnit (isometryMatrix L b g).det := by
  have h := isometryMatrix_det_mul_self L b g hdet
  exact ⟨⟨_, _, h, h⟩, rfl⟩

theorem mk''_coe (A : Matrix (Fin 2) (Fin 2) ℤ) (h : IsUnit A.det) :
    ((Matrix.GeneralLinearGroup.mk'' A h : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) = A :=
  rfl

/-- The matrix of an isometry as an element of the orthogonal group of the Gram matrix. -/
noncomputable def isometryMatrixIn (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis (Fin 2) ℤ L.obj.obj.carrier)
    (hdet : (gramMatrix L.obj b).det ≠ 0) (g : OrthogonalGroup L.obj) :
    MatrixOrthogonalGroup (gramMatrix L.obj b) := by
  classical
  refine ⟨Matrix.GeneralLinearGroup.mk'' (isometryMatrix L b g)
    (isometryMatrix_isUnit_det L b g hdet), ?_⟩
  show ((Matrix.GeneralLinearGroup.mk'' (isometryMatrix L b g)
      (isometryMatrix_isUnit_det L b g hdet) : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ).transpose * gramMatrix L.obj b *
    ((Matrix.GeneralLinearGroup.mk'' (isometryMatrix L b g)
      (isometryMatrix_isUnit_det L b g hdet) : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) = gramMatrix L.obj b
  exact isometryMatrix_gram L b g

theorem isometryMatrixIn_injective (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis (Fin 2) ℤ L.obj.obj.carrier)
    (hdet : (gramMatrix L.obj b).det ≠ 0) :
    Function.Injective (isometryMatrixIn L b hdet) := by
  intro g h hgh
  have h1 : ((isometryMatrixIn L b hdet g : MatrixOrthogonalGroup (gramMatrix L.obj b)) :
      Matrix.GeneralLinearGroup (Fin 2) ℤ) = (isometryMatrixIn L b hdet h).1 :=
    congrArg Subtype.val hgh
  have h2 : ((isometryMatrixIn L b hdet g).1 : Matrix (Fin 2) (Fin 2) ℤ) =
      ((isometryMatrixIn L b hdet h).1 : Matrix (Fin 2) (Fin 2) ℤ) := congrArg Units.val h1
  refine isometryMatrix_injective L b ?_
  simpa [isometryMatrixIn, mk''_coe] using h2

/-- A Gram matrix whose determinant is a nonzero square up to sign is nondegenerate. -/
theorem gramMatrix_det_ne_zero (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis (Fin 2) ℤ L.obj.obj.carrier)
    (hsq : ∃ σ : ℚ, σ ≠ 0 ∧ ((gramMatrix L.obj b).det : ℚ) = -σ ^ 2) :
    (gramMatrix L.obj b).det ≠ 0 := by
  intro h
  obtain ⟨σ, hσ, hsqσ⟩ := hsq
  rw [h, Int.cast_zero] at hsqσ
  exact hσ (pow_eq_zero_iff two_ne_zero |>.mp (by linarith))

/-- **The orthogonal group of a split binary lattice is finite.** -/
theorem finite_orthogonalGroup_of_split (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis (Fin 2) ℤ L.obj.obj.carrier)
    (hsq : ∃ σ : ℚ, σ ≠ 0 ∧ ((gramMatrix L.obj b).det : ℚ) = -σ ^ 2) :
    Finite (OrthogonalGroup L.obj) := by
  have hdet := gramMatrix_det_ne_zero L b hsq
  haveI : Finite (MatrixOrthogonalGroup (gramMatrix L.obj b)) :=
    finite_matrixOrthogonalGroup_of_symm (gramMatrix_transpose L b) hdet hsq
  exact Finite.of_injective _ (isometryMatrixIn_injective L b hdet)

/-- **The orthogonal group of a split binary lattice has at most four elements.** -/
theorem natCard_orthogonalGroup_le_four_of_split (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis (Fin 2) ℤ L.obj.obj.carrier)
    (hsq : ∃ σ : ℚ, σ ≠ 0 ∧ ((gramMatrix L.obj b).det : ℚ) = -σ ^ 2) :
    Nat.card (OrthogonalGroup L.obj) ≤ 4 := by
  have hdet := gramMatrix_det_ne_zero L b hsq
  haveI : Finite (MatrixOrthogonalGroup (gramMatrix L.obj b)) :=
    finite_matrixOrthogonalGroup_of_symm (gramMatrix_transpose L b) hdet hsq
  calc Nat.card (OrthogonalGroup L.obj)
      ≤ Nat.card (MatrixOrthogonalGroup (gramMatrix L.obj b)) :=
        Nat.card_le_card_of_injective _ (isometryMatrixIn_injective L b hdet)
    _ ≤ 4 := natCard_matrixOrthogonalGroup_le_four_of_symm (gramMatrix_transpose L b) hdet hsq

/-- **`SO(L) = {±1}`**: an isometry of a split binary lattice whose matrix in a basis has
determinant one is the identity or the negation map. -/
theorem isometry_eq_id_or_neg_of_split (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis (Fin 2) ℤ L.obj.obj.carrier)
    (hsq : ∃ σ : ℚ, σ ≠ 0 ∧ ((gramMatrix L.obj b).det : ℚ) = -σ ^ 2)
    (g : OrthogonalGroup L.obj) (hdetg : (isometryMatrix L b g).det = 1) :
    (g.1 : L.obj.obj.carrier →ₗ[ℤ] L.obj.obj.carrier) = LinearMap.id ∨
      (g.1 : L.obj.obj.carrier →ₗ[ℤ] L.obj.obj.carrier) = -LinearMap.id := by
  have hdet := gramMatrix_det_ne_zero L b hsq
  have hmat : (LinearMap.toMatrix b b)
      (g.1 : L.obj.obj.carrier →ₗ[ℤ] L.obj.obj.carrier) = 1 ∨
      (LinearMap.toMatrix b b)
        (g.1 : L.obj.obj.carrier →ₗ[ℤ] L.obj.obj.carrier) = -1 :=
    isometry_eq_pm_one_of_neg_det_isSquare_of_symm (gramMatrix_transpose L b) hdet hsq
      (isometryMatrix_gram L b g) hdetg
  rcases hmat with h | h
  · left
    refine linearMap_eq_of_toMatrix_eq b ?_
    rw [h, show (LinearMap.toMatrix b b)
      (LinearMap.id : L.obj.obj.carrier →ₗ[ℤ] L.obj.obj.carrier) = 1 from by simp]
  · right
    refine linearMap_eq_of_toMatrix_eq b ?_
    rw [h, show (LinearMap.toMatrix b b)
      (-(LinearMap.id : L.obj.obj.carrier →ₗ[ℤ] L.obj.obj.carrier)) = -1 from by simp]

end LeanCategories.Lattices.Valued

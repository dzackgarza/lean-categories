/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Signature
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Representation numbers and theta series

The vectors of a fixed value in a positive definite integral lattice form a finite set. A chosen
integral basis realizes the lattice as the standard integral points of a real coordinate space, in
which the real Gram matrix is positive definite. A positive definite matrix factors as `BᴴB` with
`B` invertible, so a value level set of the associated quadratic form is the image of a ball under
a linear map, hence bounded. The integral points are discrete, so the level set of a lattice value
is finite. Counting those vectors gives the representation numbers, and their generating power
series is the theta series.
-/

@[expose] public section

noncomputable section

open Matrix

namespace LeanCategories.Lattices.Valued

/-- A positive definite signature makes the matrix quadratic form positive definite. -/
theorem matrixQuadraticForm_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (h : IsPositiveDefiniteSignature (matrixSignature ℝ A)) :
    (matrixQuadraticForm ℝ A).PosDef := by
  obtain ⟨hneg, hrad⟩ := h
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := matrixQuadraticForm ℝ A)
  obtain ⟨V, hV, hVpos⟩ := exists_finrank_eq_sigPos_and_posDef (matrixQuadraticForm ℝ A)
  have hVtop : V = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    change sigNeg (matrixQuadraticForm ℝ A) = 0 at hneg
    change Module.finrank ℝ (matrixQuadraticForm ℝ A).radical = 0 at hrad
    rw [hV]
    omega
  subst hVtop
  intro x hx
  have hres := hVpos (x := ⟨x, Submodule.mem_top⟩) (by simpa using hx)
  simpa using hres

open scoped MatrixOrder in
/-- Level sets of a positive definite matrix quadratic form are bounded. -/
theorem isBounded_setOf_dotProduct_mulVec {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (r : ℝ) :
    Bornology.IsBounded {v : ι → ℝ | v ⬝ᵥ A *ᵥ v = r} := by
  classical
  obtain ⟨B, hB⟩ :=
    (CStarAlgebra.nonneg_iff_eq_star_mul_self (A := Matrix ι ι ℝ)).mp hA.posSemidef.nonneg
  have hBdet : IsUnit B.det := by
    rw [isUnit_iff_ne_zero]
    intro hzero
    have : A.det = 0 := by
      rw [hB, star_eq_conjTranspose, det_mul, det_conjTranspose, hzero]
      simp
    exact absurd this (ne_of_gt hA.det_pos)
  have hquad (v : ι → ℝ) : v ⬝ᵥ A *ᵥ v = (B *ᵥ v) ⬝ᵥ (B *ᵥ v) := by
    rw [hB, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      ← mulVec_mulVec, dotProduct_transpose_mulVec]
  refine Bornology.IsBounded.subset (LipschitzWith.isBounded_image
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin B⁻¹)).lipschitz
    (Metric.isBounded_closedBall (x := (0 : ι → ℝ)) (r := Real.sqrt r))) ?_
  intro v hv
  have hvr : (B *ᵥ v) ⬝ᵥ (B *ᵥ v) = r := (hquad v).symm.trans hv
  refine ⟨B *ᵥ v, ?_, ?_⟩
  · simp only [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg r)).2 fun i ↦ ?_
    have hle : (B *ᵥ v) i * (B *ᵥ v) i ≤ r := by
      rw [← hvr]
      exact Finset.single_le_sum (f := fun j ↦ (B *ᵥ v) j * (B *ᵥ v) j)
        (fun j _ ↦ mul_self_nonneg _) (Finset.mem_univ i)
    calc ‖(B *ᵥ v) i‖ = Real.sqrt ((B *ᵥ v) i * (B *ᵥ v) i) := by
          rw [Real.norm_eq_abs, ← Real.sqrt_mul_self_eq_abs]
      _ ≤ Real.sqrt r := Real.sqrt_le_sqrt hle
  · change B⁻¹ *ᵥ (B *ᵥ v) = v
    rw [mulVec_mulVec, nonsing_inv_mul B hBdet, one_mulVec]

namespace FiniteProjectiveLatticeCat

/-- The real Gram matrix of an integral lattice in a chosen integral basis. -/
def realGramMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : FiniteProjectiveLatticeCat ℤ ℤ) (b : Module.Basis ι ℤ L.obj.obj.carrier) :
    Matrix ι ι ℝ :=
  (gramMatrix L.obj b).map (Int.castRingHom ℝ)

/-- The real coordinate vector of a lattice element in a chosen integral basis. -/
def realCoord {ι : Type*} (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis ι ℤ L.obj.obj.carrier) (x : L.obj.obj.carrier) : ι → ℝ :=
  fun i ↦ ((b.repr x i : ℤ) : ℝ)

/-- The zero vector has zero coordinates. -/
@[simp]
theorem realCoord_zero {ι : Type*} (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis ι ℤ L.obj.obj.carrier) : L.realCoord b 0 = 0 := by
  funext i
  simp [realCoord]

/-- Distinct lattice elements have distinct real coordinate vectors. -/
theorem realCoord_injective {ι : Type*} (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis ι ℤ L.obj.obj.carrier) : Function.Injective (L.realCoord b) := by
  intro x y hxy
  refine b.repr.injective (Finsupp.ext fun i ↦ ?_)
  exact Int.cast_injective (α := ℝ) (congrFun hxy i)

/-- The lattice value of a vector is the real Gram quadratic form of its coordinates. -/
theorem realCoord_dotProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : FiniteProjectiveLatticeCat ℤ ℤ) (b : Module.Basis ι ℤ L.obj.obj.carrier)
    (x : L.obj.obj.carrier) :
    L.realCoord b x ⬝ᵥ L.realGramMatrix b *ᵥ L.realCoord b x =
      ((L.obj.obj.pairing x x : ℤ) : ℝ) := by
  have hint : L.obj.obj.pairing x x =
      ∑ i, ∑ j, b.repr x i * gramMatrix L.obj b i j * b.repr x j := by
    rw [show L.obj.obj.pairing x x = L.obj.obj.bilinMap x x from rfl,
      ← Matrix.toBilin_toMatrix b L.obj.obj.bilinMap, Matrix.toBilin_apply]
    rfl
  rw [hint]
  push_cast
  simp only [realGramMatrix, realCoord, dotProduct, Matrix.mulVec, Matrix.map_apply,
    eq_intCast, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- The real Gram matrix of a positive definite lattice is positive definite. -/
theorem realGramMatrix_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : FiniteProjectiveLatticeCat ℤ ℤ) (hL : IsPositiveDefiniteLattice L)
    (b : Module.Basis ι ℤ L.obj.obj.carrier) : (L.realGramMatrix b).PosDef := by
  have hsig : IsPositiveDefiniteSignature (matrixSignature ℝ (L.realGramMatrix b)) := by
    rw [realGramMatrix, ← integralSignature_eq_matrixSignature L b]
    exact hL
  have hQ := matrixQuadraticForm_posDef (L.realGramMatrix b) hsig
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx ↦ ?_
  · ext i j
    simp only [realGramMatrix, Matrix.map_apply, eq_intCast, Matrix.conjTranspose_apply,
      star_trivial]
    congr 1
    simp only [gramMatrix, LinearMap.BilinForm.toMatrix_apply]
    exact L.obj.property.2 (b j) (b i)
  · have hpos := hQ x hx
    simpa [matrixQuadraticForm, Matrix.toBilin'_apply'] using hpos

/-- The vectors of a lattice whose value under its own pairing is a given integer. -/
def representationSet (L : FiniteProjectiveLatticeCat ℤ ℤ) (n : ℤ) :
    Set L.obj.obj.carrier :=
  {x | L.obj.obj.pairing x x = n}

/-- Membership in a representation set is the value condition. -/
@[simp]
theorem mem_representationSet {L : FiniteProjectiveLatticeCat ℤ ℤ} {n : ℤ}
    {x : L.obj.obj.carrier} :
    x ∈ L.representationSet n ↔ L.obj.obj.pairing x x = n :=
  Iff.rfl

/-- A nonzero vector of a positive definite lattice has a positive value. -/
theorem pairing_self_pos (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsPositiveDefiniteLattice L) {x : L.obj.obj.carrier} (hx : x ≠ 0) :
    0 < L.obj.obj.pairing x x := by
  classical
  letI : Module.Free ℤ L.obj.obj.carrier := L.carrier_free
  letI : Module.Finite ℤ L.obj.obj.carrier := L.property
  set b := Module.Free.chooseBasis ℤ L.obj.obj.carrier with hb
  have hcoord : L.realCoord b x ≠ 0 := by
    simpa using (L.realCoord_injective b).ne_iff.mpr hx
  have hpos := (L.realGramMatrix_posDef hL b).dotProduct_mulVec_pos hcoord
  rw [star_trivial, L.realCoord_dotProduct b x] at hpos
  exact_mod_cast hpos

/-- Only the zero vector of a positive definite lattice has value zero. -/
theorem representationSet_zero (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsPositiveDefiniteLattice L) : L.representationSet 0 = {0} := by
  ext x
  simp only [mem_representationSet, Set.mem_singleton_iff]
  constructor
  · intro hxz
    by_contra hx
    exact absurd hxz (ne_of_gt (L.pairing_self_pos hL hx))
  · rintro rfl
    simp

/-- The vectors of a fixed value in a positive definite lattice form a finite set. -/
theorem representationSet_finite (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsPositiveDefiniteLattice L) (n : ℤ) : (L.representationSet n).Finite := by
  classical
  letI : Module.Free ℤ L.obj.obj.carrier := L.carrier_free
  letI : Module.Finite ℤ L.obj.obj.carrier := L.property
  set b := Module.Free.chooseBasis ℤ L.obj.obj.carrier with hb
  refine Set.Finite.of_finite_image (f := L.realCoord b) ?_ (L.realCoord_injective b).injOn
  refine Set.Finite.subset (ZSpan.setFinite_inter
    (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L.obj.obj.carrier))
    (isBounded_setOf_dotProduct_mulVec (L.realGramMatrix_posDef hL b) (n : ℝ))) ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨?_, ?_⟩
  · change L.realCoord b x ⬝ᵥ L.realGramMatrix b *ᵥ L.realCoord b x = (n : ℝ)
    rw [L.realCoord_dotProduct b x, mem_representationSet.mp hx]
  · rw [SetLike.mem_coe, Module.Basis.mem_span_iff_repr_mem]
    exact fun i ↦ ⟨b.repr x i, by simp [realCoord]⟩

/-- The number of lattice vectors of a given value. -/
def representationNumber (L : FiniteProjectiveLatticeCat ℤ ℤ) (n : ℤ) : ℕ :=
  (L.representationSet n).ncard

/-- A positive definite lattice has exactly one vector of value zero. -/
theorem representationNumber_zero (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsPositiveDefiniteLattice L) : L.representationNumber 0 = 1 := by
  rw [representationNumber, L.representationSet_zero hL, Set.ncard_singleton]

/-- The generating power series of the representation numbers. -/
def thetaSeries (L : FiniteProjectiveLatticeCat ℤ ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun k ↦ (L.representationNumber k : ℤ)

/-- The coefficients of the theta series are the representation numbers. -/
@[simp]
theorem coeff_thetaSeries (L : FiniteProjectiveLatticeCat ℤ ℤ) (k : ℕ) :
    PowerSeries.coeff k L.thetaSeries = (L.representationNumber k : ℤ) :=
  PowerSeries.coeff_mk k _

/-- The theta series of a positive definite lattice has constant coefficient one. -/
theorem coeff_thetaSeries_zero (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsPositiveDefiniteLattice L) : PowerSeries.coeff 0 L.thetaSeries = 1 := by
  rw [coeff_thetaSeries, Nat.cast_zero, L.representationNumber_zero hL, Nat.cast_one]

end FiniteProjectiveLatticeCat

end LeanCategories.Lattices.Valued

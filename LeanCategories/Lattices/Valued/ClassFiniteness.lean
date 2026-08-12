/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Theta
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# A Hermite bound for positive definite integral lattices

A positive definite lattice has a nonzero vector whose value is bounded by an explicit function of
the rank and the Gram determinant. The route is Minkowski's convex body theorem.

A positive definite real Gram matrix `A` factors as `Bᵀ * B` with `B` invertible, so the value of a
coordinate vector `v` is the squared euclidean length of `B *ᵥ v`. The image under `B⁻¹` of the
closed cube of half side `t` is convex, compact and symmetric, and its volume is
`(2 * t) ^ n / |det B|`. Take `t = |det B| ^ (1 / n)` and that volume becomes `2 ^ n`, which is the
covolume of the standard integral lattice of `ℝ ^ n` multiplied by `2 ^ n`. Minkowski's theorem for
a compact body then gives a nonzero integral vector `v` whose image `B *ᵥ v` has all coordinates at
most `t`, so the value of `v` is at most `n * t ^ 2 = n * (det A) ^ (1 / n)`.

Reading this back through an integral basis gives `exists_ne_zero_pairing_le`: a positive definite
integral lattice of rank `n` and Gram determinant `d` has a nonzero vector of value at most
`n * d ^ (1 / n)`.

The constant `n` is larger than Hermite's `(4 / 3) ^ ((n - 1) / 2)` and than the constant that comes
from the volume of a euclidean ball, because a cube replaces the ball. It is explicit, which is what
reduction theory needs.

Finiteness of the class set of a genus is not proved here. On top of this bound it needs a reduction
theory: an induction on the rank that splits off a minimal vector and bounds each Gram entry of a
reduced basis by a function of the rank and the determinant. Only then do the reduced Gram matrices
form a finite set of integer matrices.
-/

@[expose] public section

noncomputable section

open Matrix MeasureTheory

namespace LeanCategories.Lattices.Valued

open scoped MatrixOrder in
/-- A positive definite real matrix is `Bᵀ * B` for an invertible `B`. -/
theorem posDef_exists_transpose_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) : ∃ B : Matrix ι ι ℝ, A = Bᵀ * B ∧ B.det ≠ 0 := by
  obtain ⟨B, hB⟩ :=
    (CStarAlgebra.nonneg_iff_eq_star_mul_self (A := Matrix ι ι ℝ)).mp hA.posSemidef.nonneg
  refine ⟨B, ?_, ?_⟩
  · rw [hB, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  · intro hzero
    have hdet : A.det = 0 := by
      rw [hB, star_eq_conjTranspose, det_mul, det_conjTranspose, hzero]
      simp
    exact absurd hdet (ne_of_gt hA.det_pos)

/-- The closed cube of half side `t` in a real coordinate space. -/
def realCube (ι : Type*) (t : ℝ) : Set (ι → ℝ) :=
  Set.univ.pi fun _ ↦ Set.Icc (-t) t

/-- Membership in the closed cube is a coordinatewise bound. -/
theorem mem_realCube {ι : Type*} {t : ℝ} {v : ι → ℝ} :
    v ∈ realCube ι t ↔ ∀ i, v i ∈ Set.Icc (-t) t := by
  simp [realCube, Pi.le_def, forall_and]

/-- The closed cube is convex. -/
theorem convex_realCube (ι : Type*) (t : ℝ) : Convex ℝ (realCube ι t) :=
  convex_pi fun _ _ ↦ convex_Icc _ _

/-- The closed cube is compact. -/
theorem isCompact_realCube (ι : Type*) [Finite ι] (t : ℝ) : IsCompact (realCube ι t) :=
  isCompact_univ_pi fun _ ↦ isCompact_Icc

/-- The closed cube is symmetric about the origin. -/
theorem neg_mem_realCube {ι : Type*} {t : ℝ} {v : ι → ℝ} (hv : v ∈ realCube ι t) :
    -v ∈ realCube ι t := by
  refine mem_realCube.2 fun i ↦ ?_
  obtain ⟨h₁, h₂⟩ := mem_realCube.1 hv i
  exact ⟨by simpa using neg_le_neg h₂, by simpa using neg_le_neg h₁⟩

/-- The volume of the closed cube of half side `t` is `(2 * t) ^ n`. -/
theorem volume_realCube {ι : Type*} [Fintype ι] (t : ℝ) :
    volume (realCube ι t) = ENNReal.ofReal (2 * t) ^ Fintype.card ι := by
  rw [realCube, volume_pi_pi]
  simp [Real.volume_Icc, two_mul, sub_neg_eq_add]

/-- **Minkowski's bound for a positive definite real matrix.** The quadratic form of a positive
definite matrix `A` of size `n` takes a value at most `n * (det A) ^ (1 / n)` at some nonzero
integral vector. -/
theorem exists_intVec_ne_zero_dotProduct_mulVec_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (hcard : 0 < Fintype.card ι) :
    ∃ v : ι → ℤ, v ≠ 0 ∧
      (fun i ↦ (v i : ℝ)) ⬝ᵥ A *ᵥ (fun i ↦ (v i : ℝ)) ≤
        Fintype.card ι * A.det ^ ((Fintype.card ι : ℝ)⁻¹) := by
  classical
  haveI : Nonempty ι := Fintype.card_pos_iff.mp hcard
  obtain ⟨B, hAB, hBdet⟩ := posDef_exists_transpose_mul_self hA
  set n := Fintype.card ι with hn
  have hn0 : n ≠ 0 := hcard.ne'
  have hBabs : 0 < |B.det| := abs_pos.mpr hBdet
  set t : ℝ := |B.det| ^ ((n : ℝ)⁻¹) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hBabs _
  have htn : t ^ n = |B.det| := Real.rpow_inv_natCast_pow hBabs.le hn0
  have hquad (v : ι → ℝ) : v ⬝ᵥ A *ᵥ v = (B *ᵥ v) ⬝ᵥ (B *ᵥ v) := by
    rw [hAB, ← mulVec_mulVec, dotProduct_transpose_mulVec]
  -- The convex body: the image under `B⁻¹` of the closed cube of half side `t`.
  set f : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := Matrix.toLin' B⁻¹ with hf
  set S : Set (ι → ℝ) := f '' realCube ι t with hS
  have hfdet : |LinearMap.det f| = |B.det|⁻¹ := by
    rw [hf, LinearMap.det_toLin', Matrix.det_nonsing_inv, Ring.inverse_eq_inv', abs_inv]
  have hSvol : volume S = 2 ^ n := by
    rw [hS, MeasureTheory.Measure.addHaar_image_linearMap, hfdet, volume_realCube,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    have hval : |B.det|⁻¹ * (2 * t) ^ n = 2 ^ n := by
      rw [mul_pow, htn]
      field_simp
    rw [← hn, hval, ENNReal.ofReal_pow (by norm_num)]
    norm_num
  have hSsymm : ∀ y ∈ S, -y ∈ S := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨-z, neg_mem_realCube hz, by simp⟩
  haveI : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))))
  have hfund := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ ι) (volume : Measure (ι → ℝ))
  have hcov : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi_pi]
    simp
  have hrank : Module.finrank ℝ (ι → ℝ) = n := by simp [hn]
  obtain ⟨x, hx0, hxS⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      (μ := (volume : Measure (ι → ℝ))) hfund hSsymm ((convex_realCube ι t).linear_image f)
      ((isCompact_realCube ι t).image (LinearMap.continuous_of_finiteDimensional f))
      (by rw [hcov, hrank, hSvol, one_mul])
  obtain ⟨y, hy, hyx⟩ := hxS
  have hxspan : ((x : ι → ℝ)) ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) := x.2
  choose v hv using fun i ↦ ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ _).mp hxspan i
  have hcoord : (fun i ↦ ((v i : ℤ) : ℝ)) = ((x : ι → ℝ)) := by
    funext i
    simpa using hv i
  have hxne : ((x : ι → ℝ)) ≠ 0 := fun h ↦ hx0 (Subtype.ext h)
  refine ⟨v, ?_, ?_⟩
  · intro hzero
    refine hxne ?_
    rw [← hcoord]
    funext i
    simp [hzero]
  rw [hcoord, hquad]
  have hBx : B *ᵥ ((x : ι → ℝ)) = y := by
    rw [← hyx]
    change B *ᵥ (B⁻¹ *ᵥ y) = y
    rw [mulVec_mulVec, mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hBdet), one_mulVec]
  have hsq : t ^ 2 = A.det ^ ((n : ℝ)⁻¹) := by
    have hdetA : A.det = |B.det| ^ (2 : ℕ) := by
      rw [hAB, det_mul, det_transpose, ← sq, sq_abs]
    rw [hdetA, ht, ← Real.rpow_natCast (|B.det| ^ ((n : ℝ)⁻¹)) 2,
      ← Real.rpow_natCast |B.det| 2, ← Real.rpow_mul hBabs.le, ← Real.rpow_mul hBabs.le,
      mul_comm]
  rw [hBx, ← hsq]
  calc y ⬝ᵥ y = ∑ i, y i * y i := rfl
    _ ≤ ∑ _i : ι, t ^ 2 := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        obtain ⟨h₁, h₂⟩ := mem_realCube.1 hy i
        rw [← sq]
        exact sq_le_sq' h₁ h₂
    _ = n * t ^ 2 := by simp [hn]

namespace FiniteProjectiveLatticeCat

/-- **Hermite's bound.** A positive definite integral lattice of rank `n` and Gram determinant `d`
has a nonzero vector of value at most `n * d ^ (1 / n)`. -/
theorem exists_ne_zero_pairing_le (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : IsPositiveDefiniteLattice L) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ L.obj.obj.carrier) (hrank : 0 < L.rank) :
    ∃ x : L.obj.obj.carrier, x ≠ 0 ∧
      ((L.obj.obj.pairing x x : ℤ) : ℝ) ≤
        L.rank * ((determinant L.obj b : ℤ) : ℝ) ^ ((L.rank : ℝ)⁻¹) := by
  classical
  have hcard : L.rank = Fintype.card ι := L.rank_eq_card_basis b
  have hdet : (L.realGramMatrix b).det = ((determinant L.obj b : ℤ) : ℝ) := by
    rw [realGramMatrix, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simp [determinant]
  obtain ⟨v, hv0, hvle⟩ :=
    exists_intVec_ne_zero_dotProduct_mulVec_le (L.realGramMatrix_posDef hL b)
      (hcard ▸ hrank)
  have hrepr (i : ι) : b.repr (b.equivFun.symm v) i = v i := by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨b.equivFun.symm v, ?_, ?_⟩
  · intro hzero
    refine hv0 ?_
    have h := congrArg b.equivFun hzero
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h
  have hcoord : L.realCoord b (b.equivFun.symm v) = fun i ↦ ((v i : ℤ) : ℝ) := by
    funext i
    simp only [realCoord, hrepr]
  rw [← L.realCoord_dotProduct b, hcoord, hcard, ← hdet]
  exact hvle

end FiniteProjectiveLatticeCat

end LeanCategories.Lattices.Valued

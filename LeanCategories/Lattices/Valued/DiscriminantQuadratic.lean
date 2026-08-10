/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Discriminant
public import LeanCategories.Lattices.Valued.ScaleAndEvenness
public import LeanCategories.Modules.Quadratic.Valued.Torsion
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable (R : Type u) [CommRing R] [IsDomain R]

/-- The linear map `R → Frac(R)` with image `2R`. -/
def doubleAlgebraMap : R →ₗ[R] FractionRing R :=
  (Algebra.linearMap R (FractionRing R)).comp
    ((2 : R) • LinearMap.id)

/-- The value module `Frac(R) / 2R`. -/
abbrev DoubleFractionValueQuotient :=
  FractionRing R ⧸ LinearMap.range (doubleAlgebraMap R)

/-- The quotient map `Frac(R) → Frac(R) / 2R`. -/
def doubleFractionValueProjection :
    FractionRing R →ₗ[R] DoubleFractionValueQuotient R :=
  Submodule.mkQ (LinearMap.range (doubleAlgebraMap R))

/-- Multiplication by two on the fraction ring. -/
def twiceFraction : FractionRing R →ₗ[R] FractionRing R :=
  LinearMap.lsmul R (FractionRing R) (2 : R)

/-- The map `Frac(R) / R → Frac(R) / 2R` induced by multiplication by two. -/
def doubleValueMap :
    FractionValueQuotient R →ₗ[R] DoubleFractionValueQuotient R :=
  Submodule.mapQ
    (LinearMap.range (Algebra.linearMap R (FractionRing R)))
    (LinearMap.range (doubleAlgebraMap R))
    (twiceFraction R) (by
      rintro _ ⟨r, rfl⟩
      refine ⟨r, ?_⟩
      simp [twiceFraction, doubleAlgebraMap, Algebra.smul_def])

/-- Multiplication by two on the fraction ring, when two is nonzero. -/
noncomputable def twiceFractionEquiv [NeZero (2 : R)] :
    FractionRing R ≃ₗ[R] FractionRing R := by
  apply LinearEquiv.ofBijective (twiceFraction R)
  have htwo : algebraMap R (FractionRing R) (2 : R) ≠ 0 :=
    by
      simpa using (IsFractionRing.injective R (FractionRing R)).ne
        (NeZero.ne (2 : R))
  constructor
  · intro x y hxy
    simp only [twiceFraction, LinearMap.lsmul_apply, Algebra.smul_def] at hxy
    exact mul_left_cancel₀ htwo hxy
  · intro y
    refine ⟨(algebraMap R (FractionRing R) (2 : R))⁻¹ * y, ?_⟩
    simp only [twiceFraction, LinearMap.lsmul_apply, Algebra.smul_def]
    rw [← mul_assoc, mul_inv_cancel₀ htwo, one_mul]

/-- Multiplication by two identifies `Frac(R) / R` with `Frac(R) / 2R`. -/
noncomputable def doubleValueEquiv [NeZero (2 : R)] :
    FractionValueQuotient R ≃ₗ[R] DoubleFractionValueQuotient R :=
  Submodule.Quotient.equiv
    (LinearMap.range (Algebra.linearMap R (FractionRing R)))
    (LinearMap.range (doubleAlgebraMap R))
    (twiceFractionEquiv R) (by
      ext x
      constructor
      · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
        exact ⟨r, by
          simp [twiceFractionEquiv, twiceFraction, doubleAlgebraMap,
            Algebra.smul_def]⟩
      · rintro ⟨r, rfl⟩
        exact ⟨algebraMap R (FractionRing R) r, ⟨r, rfl⟩, by
          simp [twiceFractionEquiv, twiceFraction, doubleAlgebraMap,
            Algebra.smul_def]⟩)

@[simp]
theorem doubleValueEquiv_mk [NeZero (2 : R)] (x : FractionRing R) :
    doubleValueEquiv R (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (twiceFraction R x) :=
  rfl

/-- The quotient map by multiplication by two is the canonical equivalence. -/
theorem doubleValueMap_eq_doubleValueEquiv [NeZero (2 : R)] :
    doubleValueMap R = (doubleValueEquiv R).toLinearMap := by
  ext x
  rfl

omit [IsDomain R] in
@[simp]
theorem doubleValueMap_mk (x : FractionRing R) :
    doubleValueMap R (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (twiceFraction R x) :=
  rfl

omit [IsDomain R] in
@[simp]
theorem doubleFractionValueProjection_double (r : R) :
    doubleFractionValueProjection R
        (algebraMap R (FractionRing R) (2 : R) *
          algebraMap R (FractionRing R) r) = 0 := by
  rw [doubleFractionValueProjection, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  refine ⟨r, ?_⟩
  simp [doubleAlgebraMap, Algebra.smul_def]

omit [IsDomain R] in
theorem doubleFractionValueProjection_algebraMap_of_even
    (r : R) (hr : r ∈ Ideal.span {(2 : R)}) :
    doubleFractionValueProjection R
        (algebraMap R (FractionRing R) r) = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hr
  simpa [map_mul, mul_comm] using doubleFractionValueProjection_double R c

variable {R}
variable (L : IntegralLatticeCat R)

/-- The Riesz norm with values reduced modulo `2R`. -/
noncomputable def projectedRieszQuadraticMap
    (hL : IsGenericallyNondegenerate R L) :
    QuadraticMap R L.obj.valueDual (DoubleFractionValueQuotient R) :=
  (doubleFractionValueProjection R).compQuadraticMap
    (LinearMap.BilinMap.toQuadraticMap (rieszDualBilinMap R L hL))

omit [IsDomain R] in
/-- Evenness makes the adjoint image invisible to the projected Riesz norm. -/
theorem adjointRange_le_projectedRieszQuadraticRadical
    (hL : IsGenericallyNondegenerate R L) (hEven : IsEven L) :
    LinearMap.range L.obj.adjoint ≤
      (projectedRieszQuadraticMap L hL).radical := by
  rintro _ ⟨x, rfl⟩
  change projectedRieszQuadraticMap L hL (L.obj.adjoint x) = 0 ∧
    (projectedRieszQuadraticMap L hL).polarBilin
      (L.obj.adjoint x) = 0
  constructor
  · change doubleFractionValueProjection R
      (rieszDualBilinMap R L hL (L.obj.adjoint x)
        (L.obj.adjoint x)) = 0
    rw [rieszDualBilinMap_adjoint]
    apply doubleFractionValueProjection_algebraMap_of_even
    exact (isQuadraticallyEven_iff_value_mem L
      (Ideal.span {(2 : R)})).mp hEven x
  · apply LinearMap.ext
    intro f
    change doubleFractionValueProjection R
      (QuadraticMap.polar
        (LinearMap.BilinMap.toQuadraticMap (rieszDualBilinMap R L hL))
        (L.obj.adjoint x) f) = 0
    rw [LinearMap.BilinMap.polar_toQuadraticMap]
    rw [rieszDualBilinMap_adjoint_left, rieszDualBilinMap_adjoint_right]
    rw [← map_add]
    rw [show f x + f x = (2 : R) * f x by ring, map_mul]
    exact doubleFractionValueProjection_double R (f x)

/-- The quadratic discriminant map `q_A : A_L → Frac(R) / 2R`. -/
noncomputable def evenDiscriminantQuadraticMap
    (hL : IsGenericallyNondegenerate R L) (hEven : IsEven L) :
    QuadraticMap R L.obj.defect (DoubleFractionValueQuotient R) :=
  (projectedRieszQuadraticMap L hL).lift
    (LinearMap.range L.obj.adjoint)
    (adjointRange_le_projectedRieszQuadraticRadical L hL hEven)

omit [IsDomain R] in
@[simp]
theorem evenDiscriminantQuadraticMap_mk
    (hL : IsGenericallyNondegenerate R L) (hEven : IsEven L)
    (f : L.obj.valueDual) :
    evenDiscriminantQuadraticMap L hL hEven (Submodule.Quotient.mk f) =
      doubleFractionValueProjection R (rieszDualBilinMap R L hL f f) :=
  rfl

omit [IsDomain R] in
/-- The polarization of `q_A` is twice the discriminant bilinear form. -/
theorem evenDiscriminantQuadraticMap_polar
    (hL : IsGenericallyNondegenerate R L) (hEven : IsEven L)
    (x y : L.obj.defect) :
    QuadraticMap.polar (evenDiscriminantQuadraticMap L hL hEven) x y =
      doubleValueMap R (discriminantBilinMap R L hL x y) := by
  induction x using Submodule.Quotient.induction_on with
  | _ f =>
      induction y using Submodule.Quotient.induction_on with
      | _ g =>
          rw [QuadraticMap.polar]
          rw [← Submodule.Quotient.mk_add]
          rw [evenDiscriminantQuadraticMap_mk,
            evenDiscriminantQuadraticMap_mk,
            evenDiscriminantQuadraticMap_mk,
            discriminantBilinMap_mk]
          simp only [map_add, LinearMap.add_apply]
          rw [rieszDualBilinMap_isSymmetric R L hL g f]
          change _ = doubleFractionValueProjection R
            (twiceFraction R (rieszDualBilinMap R L hL f g))
          change _ = doubleFractionValueProjection R
            ((2 : R) • rieszDualBilinMap R L hL f g)
          rw [map_smul]
          simp [two_smul]
          abel

/-- The quadratic discriminant module of an even lattice. -/
noncomputable def evenDiscriminantQuadraticObject
    (hL : IsGenericallyNondegenerate R L) (hEven : IsEven L) :
    QuadModuleCat R (DoubleFractionValueQuotient R) :=
  QuadModuleCat.ofQuadraticMap (evenDiscriminantQuadraticMap L hL hEven)

/-- An even discriminant form with finite torsion carrier. -/
noncomputable def evenDiscriminantQuadraticFormModule
    [Module.Finite R L.obj.carrier]
    (hL : IsGenericallyNondegenerate R L) (hEven : IsEven L)
    (hT : Module.IsTorsion R L.obj.defect) :
    FiniteTorsionQuadModuleCat R (DoubleFractionValueQuotient R) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  refine ⟨evenDiscriminantQuadraticObject L hL hEven, ?_⟩
  change Module.Finite R L.obj.defect ∧ Module.IsTorsion R L.obj.defect
  exact ⟨inferInstance, hT⟩

/-- The finite torsion quadratic discriminant form of an even integer lattice. -/
noncomputable def evenDiscriminantQuadraticFormModuleInt
    (L : IntegralLatticeCat ℤ) [Module.Finite ℤ L.obj.carrier]
    (hL : IsGenericallyNondegenerate ℤ L) (hEven : IsEven L) :=
  evenDiscriminantQuadraticFormModule L hL hEven
    (discriminant_isTorsion_int L hL)

end LeanCategories.Lattices.Valued

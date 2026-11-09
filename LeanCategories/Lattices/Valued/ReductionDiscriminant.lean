/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.EvenReduction
public import LeanCategories.Lattices.Valued.DiscriminantIsotropic
public import LeanCategories.Lattices.Valued.DiscriminantQuadratic
public import LeanCategories.Lattices.Valued.SmithNormalForm
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# The discriminant form of the isotropic reduction

This module packages `Q = P^⊥/P` as a fraction-field-perfect integral lattice and exposes its
discriminant formed module. The comparison with `D^⊥/D` is constructed separately in
`IsotropicReductionDiscriminant`.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-! ## Fraction-field perfection from integral nondegeneracy -/

/-- The rationalized form of an integrally nondegenerate lattice is nondegenerate.

Denominator clearing (`exists_clear_denominator`) reduces separation over `Frac(R)` to
separation over `R`, which is the integral nondegeneracy hypothesis. -/
theorem rationalizedForm_nondegenerate_of_isNondegenerate
    (L : IntegralLatticeCat R) (hN : L.obj.IsNondegenerate) :
    (rationalizedForm R L).Nondegenerate := by
  have hrefl : (rationalizedForm R L).IsRefl := by
    intro x y
    exact fun h => by
      rw [rationalizedForm_isSymmetric R L x y] at h
      exact h
  have hleft : LinearMap.SeparatingLeft (rationalizedForm R L) := by
    intro z hz
    obtain ⟨a, ha, p, ha'⟩ := exists_clear_denominator L z
    have hp0 : p = 0 := by
      apply hN.1
      intro y
      rw [BilinModuleCat.bilinMap_apply]
      apply (FaithfulSMul.algebraMap_injective R (FractionRing R))
      rw [map_zero]
      rw [← rational_pairing_eq L p y, ← ha',
        LinearMap.BilinForm.smul_left_of_tower, hz (toRationalSpan R L y), smul_zero]
    have hz0 : a • z = 0 := by rw [ha', hp0, map_zero]
    rw [← IsScalarTower.algebraMap_smul (A := FractionRing R)] at hz0
    exact (smul_eq_zero.mp hz0).resolve_left (by
      intro h
      exact ha (FaithfulSMul.algebraMap_injective R (FractionRing R) (by simpa using h)))
  refine ⟨hleft, ?_⟩
  intro z hz
  refine hleft z (fun w => ?_)
  rw [rationalizedForm_isSymmetric R L]
  exact hz w

/-- A finite integrally nondegenerate lattice is fraction-field perfect. -/
theorem isFractionFieldPerfect_of_isNondegenerate
    (L : IntegralLatticeCat R) [Module.Finite R L.obj.carrier]
    (hN : L.obj.IsNondegenerate) :
    IsFractionFieldPerfect R L :=
  (isFractionFieldNondegenerate_iff_isFractionFieldPerfect R L).mp
    (rationalizedForm_nondegenerate_of_isNondegenerate L hN)

/-! ## The reduced lattice `Q = P^⊥/P` as a fraction-field perfect lattice -/

namespace IsotropicReductionData

variable {L : IntegralLatticeCat R} (D : IsotropicReductionData L)

/-- The reduced lattice `Q = P^⊥/P` as an integral lattice.

`EvenReduction.lean` proves that the reduced carrier is projective over a PID; together with
the descended symmetric form this is precisely the data of an `IntegralLatticeCat`. -/
noncomputable def reductionLattice [IsPrincipalIdealRing R] (hL : L.obj.IsSymmetric) :
    IntegralLatticeCat R :=
  let _ : Module.Finite R L.obj.carrier := D.finite
  ⟨D.reduction hL, reduction_projective D, D.reduction_isSymmetric hL⟩

@[simp] theorem reductionLattice_obj [IsPrincipalIdealRing R] (hL : L.obj.IsSymmetric) :
    (D.reductionLattice hL).obj = D.reduction hL :=
  rfl

/-- The form of the reduced lattice on classes. -/
@[simp] theorem reductionLattice_pairing_mk [IsPrincipalIdealRing R]
    (hL : L.obj.IsSymmetric) (x y : ↥D.perp) :
    (D.reductionLattice hL).obj.pairing (Submodule.Quotient.mk x)
        (Submodule.Quotient.mk y) =
      L.obj.pairing (x : L.obj.carrier) (y : L.obj.carrier) :=
  rfl

/-- The reduced lattice is nondegenerate: primitivity of `P` makes it the radical of the
restricted form. -/
theorem reductionLattice_isNondegenerate [IsPrincipalIdealRing R]
    (hL : L.obj.IsSymmetric) : (D.reductionLattice hL).obj.IsNondegenerate :=
  D.reduction_isNondegenerate hL

/-- The reduced carrier is torsion-free, from primitivity of `P`. -/
theorem reductionLattice_isTorsionFree [IsPrincipalIdealRing R]
    (hL : L.obj.IsSymmetric) :
    Module.IsTorsionFree R (D.reductionLattice hL).obj.carrier :=
  D.reduction_isTorsionFree

/-- The reduced carrier is finite: it is a quotient of `P^⊥`. -/
theorem reductionLattice_finite [IsPrincipalIdealRing R]
    (hL : L.obj.IsSymmetric) :
    Module.Finite R (D.reductionLattice hL).obj.carrier := by
  let _ : Module.Finite R L.obj.carrier := D.finite
  exact Module.Finite.of_surjective D.kernel.mkQ (Submodule.mkQ_surjective D.kernel)

/-- Over a PID the reduced carrier is free: it is finite and torsion-free. -/
theorem reductionLattice_isFree [IsPrincipalIdealRing R]
    (hL : L.obj.IsSymmetric) :
    Module.Free R (D.reductionLattice hL).obj.carrier := by
  let _ := D.reductionLattice_finite hL
  let _ : Module.IsTorsionFree R (D.reductionLattice hL).obj.carrier :=
    D.reductionLattice_isTorsionFree hL
  exact Module.free_of_finite_type_torsion_free'

/-- The reduced lattice `Q = P^⊥/P` is fraction-field perfect, so its discriminant form is
defined. This is the hypothesis `hQ` of the target `A_Q = discriminantBilinObject Q hQ`. -/
theorem reductionLattice_isFractionFieldPerfect [IsPrincipalIdealRing R]
    (hL : L.obj.IsSymmetric) :
    IsFractionFieldPerfect R (D.reductionLattice hL) := by
  let _ := D.reductionLattice_finite hL
  exact isFractionFieldPerfect_of_isNondegenerate _
    (D.reductionLattice_isNondegenerate hL)

/-- The discriminant form `A_Q` of the reduced lattice `Q = P^⊥/P`. -/
noncomputable def reductionDiscriminant [IsPrincipalIdealRing R]
    (hL : L.obj.IsSymmetric) :
    BilinModuleCat R (FractionValueQuotient R) :=
  discriminantBilinObject R (D.reductionLattice hL)
    (D.reductionLattice_isFractionFieldPerfect hL)

/-- `A_Q` is symmetric. -/
theorem reductionDiscriminant_isSymmetric [IsPrincipalIdealRing R]
    (hL : L.obj.IsSymmetric) :
    (D.reductionDiscriminant hL).IsSymmetric :=
  discriminantBilinObject_isSymmetric R _ (D.reductionLattice_isFractionFieldPerfect hL)

/-- `A_Q` has zero radical. -/
theorem reductionDiscriminant_isNondegenerate [IsPrincipalIdealRing R]
    (hL : L.obj.IsSymmetric) :
    (D.reductionDiscriminant hL).IsNondegenerate := by
  let _ := D.reductionLattice_finite hL
  let _ := D.reductionLattice_isFree hL
  exact discriminantBilinObject_isNondegenerate R _ (D.reductionLattice_isFractionFieldPerfect hL)

/-- `A_Q` is a perfect form. -/
theorem reductionDiscriminant_isPerfect [IsPrincipalIdealRing R]
    (hL : L.obj.IsSymmetric) :
    (D.reductionDiscriminant hL).IsPerfect := by
  let _ := D.reductionLattice_finite hL
  let _ := D.reductionLattice_isFree hL
  exact discriminantBilinObject_isPerfect R _ (D.reductionLattice_isFractionFieldPerfect hL)

/-- The pairing of two classes of the metric dual of the reduced lattice, read in `A_Q`. -/
theorem reductionDiscriminant_pairing_metricDualToDiscriminant [IsPrincipalIdealRing R]
    (hL : L.obj.IsSymmetric)
    (x y : metricDual R (D.reductionLattice hL)) :
    (D.reductionDiscriminant hL).pairing
        (metricDualToDiscriminant R (D.reductionLattice hL) x)
        (metricDualToDiscriminant R (D.reductionLattice hL) y) =
      fractionValueProjection R
        (rationalizedForm R (D.reductionLattice hL) (x : RationalSpan R (D.reductionLattice hL))
          (y : RationalSpan R (D.reductionLattice hL))) :=
  discriminant_pairing_metricDualToDiscriminant R
    (D.reductionLattice_isFractionFieldPerfect hL) x y

/-- The quadratic map of `A_Q`. -/
noncomputable def reductionDiscriminantQuadraticMap [IsPrincipalIdealRing R]
    (hL : L.obj.IsSymmetric) :
    QuadraticMap R (D.reductionLattice hL).obj.defect (FractionValueQuotient R) :=
  discriminantQuadraticMap R (D.reductionLattice hL)
    (D.reductionLattice_isFractionFieldPerfect hL)

/-- `A_Q` as a finite form module. -/
noncomputable def reductionDiscriminantFormModule [IsPrincipalIdealRing R]
    (hL : L.obj.IsSymmetric) :
    FiniteFormCat R (FractionValueQuotient R) := by
  let _ := D.reductionLattice_finite hL
  exact discriminantFormModule R (D.reductionLattice hL)
    (D.reductionLattice_isFractionFieldPerfect hL)

/-- A finite free nondegenerate lattice over `ℤ` has a finite discriminant group. -/
theorem defect_finite (L : IntegralLatticeCat ℤ) [Module.Free ℤ L.obj.carrier]
    [Module.Finite ℤ L.obj.carrier] (hL : IsFractionFieldPerfect ℤ L) :
    Finite L.obj.defect := by
  let _ : Module.Free ℤ L.obj.valueDual := inferInstance
  let _ : Module.Finite ℤ L.obj.valueDual := inferInstance
  exact Submodule.finiteQuotientOfFreeOfRankEq (LinearMap.range L.obj.adjoint)
    (adjointRange_finrank_eq_valueDual L hL)

/-- The reduced discriminant group is finite over `ℤ`. -/
noncomputable instance reductionDefectFinite {M : IntegralLatticeCat ℤ}
    (D : @IsotropicReductionData ℤ _ M)
    (hM : M.obj.IsSymmetric) : Finite (D.reductionLattice hM).obj.defect := by
  let _ : Module.Free ℤ (D.reductionLattice hM).obj.carrier := D.reductionLattice_isFree hM
  let _ : Module.Finite ℤ (D.reductionLattice hM).obj.carrier :=
    D.reductionLattice_finite hM
  exact defect_finite _ (D.reductionLattice_isFractionFieldPerfect hM)

end IsotropicReductionData

end LeanCategories.Lattices.Valued

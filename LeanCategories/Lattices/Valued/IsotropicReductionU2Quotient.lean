/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.IsotropicReductionWorkedModel
public import LeanCategories.Lattices.Valued.ReductionDiscriminant
public import LeanCategories.Lattices.Valued.IsotropicReductionDiscriminant
public import LeanCategories.Lattices.Valued.IsotropicReductionLevel

@[expose] public section

namespace LeanCategories.Lattices.Valued

open LeanCategories.Modules.Bilinear.Valued

/-- Symmetry of the model form, named to avoid an auto-bound implicit hypothesis. -/
theorem u2u_isSymmetric : u2u.obj.IsSymmetric := u2u.property.2

/-- The third basis vector in `P^⊥`. -/
def u2uPerpE : ↥u2uReductionData.perp := ⟨u2uVecE, u2uVecE_mem_perp⟩

/-- The fourth basis vector in `P^⊥`. -/
def u2uPerpF : ↥u2uReductionData.perp := ⟨u2uVecF, u2uVecF_mem_perp⟩

section DiscriminantOrthogonal

attribute [local instance 10000] u2uCarrierTorsionFree
attribute [local instance 10000] OreLocalization.instModuleOfIsScalarTower
attribute [local instance 10000] TensorProduct.instModule

/-- The class of `v/2`, as a half-integral rational vector. -/
theorem u2uHalf_coe_smul : ((u2uHalf : metricDual ℤ u2u) : RationalSpan ℤ u2u) =
    ((2 : FractionRing ℤ))⁻¹ • toRationalSpan ℤ u2u u2uVecC := by
  rw [show toRationalSpan ℤ u2u u2uVecC = ((1 : FractionRing ℤ)) ⊗ₜ[ℤ] u2uVecC from rfl]
  change ((2 : FractionRing ℤ))⁻¹ ⊗ₜ[ℤ] u2uVecC = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

attribute [local instance 10000] Submodule.Quotient.module

/-- Half-integrality criterion. -/
theorem fractionValueProjection_half_iff (n : ℤ) :
    fractionValueProjection ℤ (((2 : FractionRing ℤ))⁻¹ * algebraMap ℤ (FractionRing ℤ) n) =
      0 ↔ (2 : ℤ) ∣ n := by
  rw [fractionValueProjection, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h2 := two_fractionRing_ne_zero
    have h := congrArg (fun z => ((2 : FractionRing ℤ)) * z) hm
    simp only [← mul_assoc] at h
    rw [mul_inv_cancel₀ h2, one_mul] at h
    have h' : algebraMap ℤ (FractionRing ℤ) (2 * m) = algebraMap ℤ (FractionRing ℤ) n := by
      rw [map_mul]
      simpa using h
    exact (IsFractionRing.injective ℤ (FractionRing ℤ) h').symm
  · rintro ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    have h2 := two_fractionRing_ne_zero
    have key : (algebraMap ℤ (FractionRing ℤ)) (2 * m) =
        (algebraMap ℤ (FractionRing ℤ)) 2 * (algebraMap ℤ (FractionRing ℤ)) m := map_mul _ _ _
    rw [key]
    have hcast : (algebraMap ℤ (FractionRing ℤ)) 2 = (2 : FractionRing ℤ) := by norm_num
    have h2' : ((2 : FractionRing ℤ))⁻¹ * (algebraMap ℤ (FractionRing ℤ)) 2 = 1 := by
      rw [hcast, inv_mul_cancel₀ h2]
    rw [← mul_assoc, h2', one_mul]
    rfl

/-- Pairing with `v/2` detects the first discriminant coordinate. -/
theorem u2u_pairing_eta (x : u2u.obj.defect) :
    (discriminantBilinObject ℤ u2u u2u_isFractionFieldPerfect).pairing x u2uEta = 0 ↔
      (u2uCoord x).1 = 0 := by
  obtain ⟨y, rfl⟩ := metricDualToDiscriminant_surjective ℤ u2u u2u_isFractionFieldPerfect x
  rw [show u2uEta = metricDualToDiscriminant ℤ u2u u2uHalf from rfl,
    discriminant_pairing_metricDualToDiscriminant, u2uHalf_coe_smul,
    LinearMap.BilinForm.smul_right, ← metricDualToValueDual_apply,
    fractionValueProjection_half_iff]
  have hcoord : u2uCoord (metricDualToDiscriminant ℤ u2u y) =
      u2uCoordProj (metricDualToValueDual ℤ u2u y) := by
    change u2uCoord (Submodule.Quotient.mk (metricDualToValueDual ℤ u2u y)) = _
    rw [u2uCoord_mk]
  rw [hcoord, u2uCoordProj_apply']
  constructor
  · rintro ⟨c, hc⟩
    rw [hc, Int.cast_mul]
    simp [two_mul_zmod_two_nat]
  · intro h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (metricDualToValueDual ℤ u2u y u2uVecC) 2).mp h

/-- `D` is its own orthogonal complement in the worked model. -/
theorem u2u_isotropicDiscriminantOrthogonal_eq :
    isotropicDiscriminantOrthogonal u2u u2u_isFractionFieldPerfect u2uLine =
      isotropicDiscriminant u2u u2u_isFractionFieldPerfect u2uLine := by
  refine le_antisymm ?_ (isotropicDiscriminant_le_orthogonal u2u
    u2u_isFractionFieldPerfect u2uLine u2uLine_isotropic)
  intro x hx
  rw [isotropicDiscriminantOrthogonal, isotropicDiscriminantPerp] at hx
  rw [u2u_isotropicDiscriminant_eq_ker_firstCoord]
  have hx' : ∀ p ∈ isotropicDiscriminant u2u u2u_isFractionFieldPerfect u2uLine,
      (discriminantBilinObject ℤ u2u u2u_isFractionFieldPerfect).pairing p x = 0 :=
    (BilinModuleCat.mem_orthogonalSubmodule_iff
      (discriminantBilinObject ℤ u2u u2u_isFractionFieldPerfect)
      (isotropicDiscriminant u2u u2u_isFractionFieldPerfect u2uLine) x).mp hx
  rw [LinearMap.mem_ker, u2uFirstCoord_apply]
  refine (u2u_pairing_eta x).mp ?_
  rw [show (discriminantBilinObject ℤ u2u u2u_isFractionFieldPerfect).pairing x u2uEta =
    (discriminantBilinObject ℤ u2u u2u_isFractionFieldPerfect).pairing u2uEta x from
      discriminantBilinObject_isSymmetric ℤ u2u u2u_isFractionFieldPerfect x u2uEta]
  exact hx' u2uEta u2uEta_mem_isotropicDiscriminant

/-- The same orthogonal complement, as the kernel of the first coordinate. -/
theorem u2u_isotropicDiscriminantOrthogonal_eq_ker :
    isotropicDiscriminantOrthogonal u2u u2u_isFractionFieldPerfect u2uLine =
      LinearMap.ker u2uFirstCoord := by
  rw [u2u_isotropicDiscriminantOrthogonal_eq, u2u_isotropicDiscriminant_eq_ker_firstCoord]

end DiscriminantOrthogonal

theorem u2u_apply_add (x y : u2u.obj.carrier) (i : Fin 4) :
    (x + y) i = x i + y i := rfl

theorem u2u_apply_smul (k : ℤ) (x : u2u.obj.carrier) (i : Fin 4) :
    (k • x) i = k * x i := rfl

/-- Every vector in `P^⊥ = (e₀)^⊥` in `U(2) ⊕ U` has only three remaining coordinates. -/
theorem u2u_perp_decomp (y : u2u.obj.carrier) (hy : y ∈ u2u.obj.orthogonalSubmodule u2uLine) :
    y = y 0 • u2uVecC + y 2 • u2uVecE + y 3 • u2uVecF := by
  have hy1 : y 1 = 0 := (u2u_mem_perp_iff y).mp hy
  funext i
  fin_cases i <;>
    rw [u2u_apply_add, u2u_apply_add, u2u_apply_smul, u2u_apply_smul, u2u_apply_smul] <;>
    simp [u2uVecC_coord, u2uVecE_coord, u2uVecF_coord, u2u_vector_zero, u2u_vector_one,
      u2u_vector_two, u2u_vector_three, u2u_vectorC_zero, u2u_vectorC_one, u2u_vectorC_two,
      u2u_vectorC_three, u2u_vectorD_zero, u2u_vectorD_one, u2u_vectorD_two,
      u2u_vectorD_three, hy1]

/-- The last two coordinates on `P^⊥`. -/
def u2uPerpCoords : ↥u2uReductionData.perp →ₗ[ℤ] (Fin 2 → ℤ) where
  toFun y := ![y.1 2, y.1 3]
  map_add' _ _ := by funext i; fin_cases i <;> rfl
  map_smul' _ _ := by funext i; fin_cases i <;> rfl

/-- The last two coordinates vanish on `P`. -/
theorem u2uPerpCoords_eq_zero_of_mem_kernel {y : ↥u2uReductionData.perp}
    (hy : y ∈ u2uReductionData.kernel) : u2uPerpCoords y = 0 := by
  rw [IsotropicReductionData.mem_kernel_iff] at hy
  change y.1 ∈ u2uLine at hy
  rw [u2u_mem_line_iff] at hy
  obtain ⟨a, ha⟩ := hy
  funext i
  fin_cases i
  · change y.1 2 = 0
    rw [← ha, u2u_coord_smul, u2uVecC_two, mul_zero]
  · change y.1 3 = 0
    rw [← ha, u2u_coord_smul, u2uVecC_three, mul_zero]

/-- The coordinate map on `P^⊥/P`, with values `(y₂, y₃)`. -/
noncomputable def u2uReducedCoords :
    (↥u2uReductionData.perp ⧸ u2uReductionData.kernel) →ₗ[ℤ] (Fin 2 → ℤ) :=
  u2uReductionData.kernel.liftQ u2uPerpCoords (fun y hy => by
    change u2uPerpCoords y = 0
    exact u2uPerpCoords_eq_zero_of_mem_kernel hy)

@[simp] theorem u2uReducedCoords_mk (y : ↥u2uReductionData.perp) :
    u2uReducedCoords (Submodule.Quotient.mk y) = ![y.1 2, y.1 3] := rfl

/-- The two hyperbolic classes as elements of the quotient. -/
noncomputable def u2uReducedClass (z : Fin 2 → ℤ) :
    ↥u2uReductionData.perp ⧸ u2uReductionData.kernel :=
  Submodule.Quotient.mk
    (z 0 • u2uPerpE +
      z 1 • u2uPerpF)

/-- Reconstruction from the two hyperbolic coordinates is linear. -/
noncomputable def u2uReducedClassHom : (Fin 2 → ℤ) →ₗ[ℤ]
    (↥u2uReductionData.perp ⧸ u2uReductionData.kernel) where
  toFun := u2uReducedClass
  map_add' z w := by
    simp only [u2uReducedClass, Pi.add_apply, add_smul]
    change u2uReductionData.kernel.mkQ _ = u2uReductionData.kernel.mkQ _ +
      u2uReductionData.kernel.mkQ _
    rw [← map_add]
    congr 1
    abel
  map_smul' a z := by
    simp only [u2uReducedClass, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
    change u2uReductionData.kernel.mkQ _ = a • u2uReductionData.kernel.mkQ _
    conv_rhs => rw [← map_smul]
    congr 1
    simp only [smul_add]

@[simp] theorem u2uReducedClassHom_apply (z : Fin 2 → ℤ) :
    u2uReducedClassHom z = u2uReducedClass z := rfl

@[simp] theorem u2uReducedClass_one_zero :
    u2uReducedClass ![1, 0] = Submodule.Quotient.mk u2uPerpE := by
  simp [u2uReducedClass]

@[simp] theorem u2uReducedClass_zero_one :
    u2uReducedClass ![0, 1] = Submodule.Quotient.mk u2uPerpF := by
  simp [u2uReducedClass]

@[simp] theorem u2uReducedCoords_class (z : Fin 2 → ℤ) :
    u2uReducedCoords (u2uReducedClass z) = z := by
  funext i
  fin_cases i
  · change z 0 * (1 : ℤ) + z 1 * 0 = z 0
    simp
  · change z 0 * (0 : ℤ) + z 1 * 1 = z 1
    simp

/-- The reduced lattice has two coordinates. -/
noncomputable def u2uReducedCoordEquiv :
    (↥u2uReductionData.perp ⧸ u2uReductionData.kernel) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  LinearEquiv.ofBijective u2uReducedCoords ⟨by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).mpr (fun q hq => ?_)
    induction q using Submodule.Quotient.induction_on with
    | _ y =>
      change u2uReducedCoords (Submodule.Quotient.mk y) = 0 at hq
      have h2 : y.1 2 = 0 := congrFun hq 0
      have h3 : y.1 3 = 0 := congrFun hq 1
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [IsotropicReductionData.mem_kernel_iff]
      have hdecomp := u2u_perp_decomp y.1 y.2
      have hyP : y.1 ∈ u2uLine := by
        rw [hdecomp, h2, h3, zero_smul, zero_smul, add_zero]
        simpa using Submodule.smul_mem u2uLine (y.1 0) u2uVecC_mem_line
      exact hyP, by
    intro z
    exact ⟨u2uReducedClass z, u2uReducedCoords_class z⟩⟩

@[simp] theorem u2uReducedCoordEquiv_apply_mk (y : ↥u2uReductionData.perp) :
    u2uReducedCoordEquiv (Submodule.Quotient.mk y) = ![y.1 2, y.1 3] := rfl

@[simp] theorem u2uReducedCoordEquiv_symm_apply (z : Fin 2 → ℤ) :
    u2uReducedCoordEquiv.symm z = u2uReducedClass z := by
  apply u2uReducedCoordEquiv.injective
  rw [LinearEquiv.apply_symm_apply, u2uReducedCoordEquiv]
  exact (u2uReducedCoords_class z).symm

/-- A basis of the reduced hyperbolic plane. -/
noncomputable def u2uReductionBasis : Module.Basis (Fin 2) ℤ
    (u2uReductionData.reductionLattice u2u_isSymmetric).obj.carrier :=
  (Pi.basisFun ℤ (Fin 2)).map u2uReducedCoordEquiv.symm

theorem u2uReductionBasis_zero : u2uReductionBasis 0 =
    (Submodule.Quotient.mk u2uPerpE :
      (u2uReductionData.reductionLattice u2u_isSymmetric).obj.carrier) := by
  change (Pi.basisFun ℤ (Fin 2)).map u2uReducedCoordEquiv.symm 0 = _
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  rw [show (Pi.single (0 : Fin 2) (1 : ℤ)) = ![1, 0] by
    funext i; fin_cases i <;> simp]
  rw [u2uReducedCoordEquiv_symm_apply, u2uReducedClass_one_zero]

theorem u2uReductionBasis_one : u2uReductionBasis 1 =
    (Submodule.Quotient.mk u2uPerpF :
      (u2uReductionData.reductionLattice u2u_isSymmetric).obj.carrier) := by
  change (Pi.basisFun ℤ (Fin 2)).map u2uReducedCoordEquiv.symm 1 = _
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  rw [show (Pi.single (1 : Fin 2) (1 : ℤ)) = ![0, 1] by
    funext i; fin_cases i <;> simp]
  rw [u2uReducedCoordEquiv_symm_apply, u2uReducedClass_zero_one]

/-- The reduced Gram matrix is `[[0,1],[1,0]]`. -/
theorem u2u_reduction_gramMatrix : gramMatrix
    (u2uReductionData.reductionLattice u2u_isSymmetric) u2uReductionBasis =
    !![0, 1; 1, 0] := by
  ext i j
  rw [gramMatrix, LinearMap.BilinForm.toMatrix_apply]
  change (u2uReductionData.reductionLattice u2u_isSymmetric).obj.pairing _ _ = _
  fin_cases i <;> fin_cases j
  · change (u2uReductionData.reductionLattice u2u_isSymmetric).obj.pairing
      (u2uReductionBasis 0) (u2uReductionBasis 0) = 0
    rw [u2uReductionBasis_zero,
      u2uReductionData.reductionLattice_pairing_mk]
    exact u2u_perp_generators_hyperbolic.1
  · change (u2uReductionData.reductionLattice u2u_isSymmetric).obj.pairing
      (u2uReductionBasis 0) (u2uReductionBasis 1) = 1
    rw [u2uReductionBasis_zero, u2uReductionBasis_one,
      u2uReductionData.reductionLattice_pairing_mk]
    exact u2u_perp_generators_hyperbolic.2.1
  · change (u2uReductionData.reductionLattice u2u_isSymmetric).obj.pairing
      (u2uReductionBasis 1) (u2uReductionBasis 0) = 1
    rw [u2uReductionBasis_one, u2uReductionBasis_zero,
      u2uReductionData.reductionLattice_pairing_mk]
    exact u2u_perp_generators_hyperbolic.2.2.1
  · change (u2uReductionData.reductionLattice u2u_isSymmetric).obj.pairing
      (u2uReductionBasis 1) (u2uReductionBasis 1) = 0
    rw [u2uReductionBasis_one,
      u2uReductionData.reductionLattice_pairing_mk]
    exact u2u_perp_generators_hyperbolic.2.2.2

/-- The reduction is perfect over `ℤ`. -/
theorem u2u_reduction_isPerfect :
    (u2uReductionData.reductionLattice u2u_isSymmetric).obj.IsPerfect := by
  rw [isPerfect_iff_isUnit_determinant _ u2uReductionBasis, determinant,
    u2u_reduction_gramMatrix]
  decide

/-- The reduced adjoint is surjective. -/
theorem u2u_reduction_adjoint_surjective :
    Function.Surjective (u2uReductionData.reductionLattice u2u_isSymmetric).obj.adjoint := by
  have h := (BilinModuleCat.isPerfect_iff_adjoint_bijective_of_isSymmetric
    (u2uReductionData.reductionLattice u2u_isSymmetric).obj
    (u2uReductionData.reductionLattice u2u_isSymmetric).property.2).mp
    u2u_reduction_isPerfect
  exact h.2

/-- The discriminant group of the reduced hyperbolic plane is a subsingleton. -/
theorem u2u_reduction_discriminant_subsingleton :
    Subsingleton (u2uReductionData.reductionLattice u2u_isSymmetric).obj.defect := by
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ f =>
    induction y using Submodule.Quotient.induction_on with
    | _ g =>
      apply (Submodule.Quotient.eq _).mpr
      change f - g ∈ LinearMap.range (u2uReductionData.reductionLattice u2u_isSymmetric).obj.adjoint
      rw [LinearMap.range_eq_top.mpr u2u_reduction_adjoint_surjective]
      exact Submodule.mem_top

/-- `D^⊥/D` is trivial in the worked model because `D^⊥ = D`. -/
theorem u2u_isotropicDiscriminantSubquotient_subsingleton :
    Subsingleton (↥(isotropicDiscriminantOrthogonal u2u u2u_isFractionFieldPerfect
        u2uReductionData.submodule) ⧸
      isotropicDiscriminantInOrthogonal u2u u2u_isFractionFieldPerfect
        u2uReductionData.submodule) := by
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
    induction y using Submodule.Quotient.induction_on with
    | _ b =>
      apply (Submodule.Quotient.eq _).mpr
      change (a : u2u.obj.defect) - (b : u2u.obj.defect) ∈
        isotropicDiscriminant u2u u2u_isFractionFieldPerfect u2uLine
      have ha : (a : u2u.obj.defect) ∈
          isotropicDiscriminant u2u u2u_isFractionFieldPerfect u2uLine := by
        rw [← u2u_isotropicDiscriminantOrthogonal_eq]
        exact a.2
      have hb : (b : u2u.obj.defect) ∈
          isotropicDiscriminant u2u u2u_isFractionFieldPerfect u2uLine := by
        rw [← u2u_isotropicDiscriminantOrthogonal_eq]
        exact b.2
      exact (isotropicDiscriminant u2u u2u_isFractionFieldPerfect u2uLine).sub_mem ha hb

/-- The canonical extension comparison on the worked model is bijective. -/
theorem u2u_extendDualSubquotientHom_bijective {C : Submodule ℤ u2u.obj.carrier}
    (hsup : u2uReductionData.perp ⊔ C = ⊤) (hinf : u2uReductionData.perp ⊓ C = ⊥) :
    Function.Bijective (extendDualSubquotientHom u2uReductionData u2u_isSymmetric
      u2u_isFractionFieldPerfect hsup hinf) := by
  refine ⟨extendDualSubquotientHom_injective u2uReductionData u2u_isSymmetric
    u2u_isFractionFieldPerfect hsup hinf, ?_⟩
  intro y
  refine ⟨0, ?_⟩
  let _ := u2u_isotropicDiscriminantSubquotient_subsingleton
  exact Subsingleton.elim _ _

/-- The worked model's canonical linear equivalence between the two actual discriminant
quotient types. Here `D = D^⊥` is the nonzero subgroup `ker` of the first coordinate, and the
equivalence is the unconditional discriminant isometry of the isotropic reduction: no order
hypothesis, and no comparison of group orders, enters. -/
noncomputable def u2uExtendDualDiscriminantEquiv {C : Submodule ℤ u2u.obj.carrier}
    (hsup : u2uReductionData.perp ⊔ C = ⊤) (hinf : u2uReductionData.perp ⊓ C = ⊥) :
    (u2uReductionData.reductionLattice u2u_isSymmetric).obj.defect ≃ₗ[ℤ]
      (↥(isotropicDiscriminantOrthogonal u2u u2u_isFractionFieldPerfect u2uLine) ⧸
        isotropicDiscriminantInOrthogonal u2u u2u_isFractionFieldPerfect u2uLine) :=
  extendDualDiscriminantEquiv u2u u2uReductionData u2u_isSymmetric
    u2u_isFractionFieldPerfect hsup hinf

/-- The worked equivalence is the canonical extension map on representatives. -/
theorem u2uExtendDualDiscriminantEquiv_apply {C : Submodule ℤ u2u.obj.carrier}
    (hsup : u2uReductionData.perp ⊔ C = ⊤) (hinf : u2uReductionData.perp ⊓ C = ⊥)
    (x : (u2uReductionData.reductionLattice u2u_isSymmetric).obj.defect) :
    u2uExtendDualDiscriminantEquiv hsup hinf x =
      extendDualSubquotientHom u2uReductionData u2u_isSymmetric
        u2u_isFractionFieldPerfect hsup hinf x := by
  unfold u2uExtendDualDiscriminantEquiv extendDualDiscriminantEquiv
  rfl

end LeanCategories.Lattices.Valued

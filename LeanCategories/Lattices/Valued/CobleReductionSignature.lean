/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CobleReduction
public import LeanCategories.Lattices.Valued.ReductionDiscriminant
public import LeanCategories.Lattices.Valued.Standard
public import LeanCategories.Lattices.Valued.Signature

/-!
# The signature `(1, 8)` of the reduction `Q = e^⊥/e` of `T_Co` (#114)

`T_Co = ⟨2⟩ ⊕ U(2) ⊕ E₈(−2)`, with `e = e₁` the first isotropic vector of the `U(2)` summand. Its
orthogonal complement is the hyperplane `x₂ = 0` (`coble_perp_eq_ker`), so the classes of
`e₀, e₃, …, e₁₀` are a `ℤ`-basis of the reduction `Q = e^⊥/ℤe`: the `U(2)` summand collapses to
nothing and the `⟨2⟩` and `E₈(−2)` summands survive.

* `cobleQIndex`: the nine surviving coordinates; `cobleQVec`: the representatives;
  `cobleQCoords` and `cobleQClass`: the two coordinate maps; `cobleQCoordEquiv`: the resulting
  linear equivalence `Q ≃ₗ[ℤ] (Fin 1 ⊕ Fin 8 → ℤ)`; `cobleReductionBasis`: the basis of `Q`.
* `cobleReduction_gramMatrix`: the Gram matrix of `Q` in that basis is the block sum
  `⟨2⟩ ⊕ E₈(−2)`.
* `cobleE8Block_matrixSignature`: the `E₈(−2)` block is twice the negative `E₈` form
  (`cobleE8Block_eq`) and is negative definite of rank eight, via the scaled real root change
  `cobleE8RealChange`.
* `cobleReduction_integralSignature`: the real signature of `Q`, `integralSignature` of
  `Signature.lean`, is `(1, 8, 0)`.

Several of the coordinate lemmas mix `↥cobleLattice.obj.carrier` with `Fin 11 → ℤ`; those two
types agree only at default transparency while `rw` and matrix-literal reduction work at implicit
transparency, so `backward.isDefEq.respectTransparency` is turned off locally, declaration by
declaration, where the two types meet.
-/

@[expose] public section

open Matrix
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-! ## The `E₈(−2)` block of the Gram matrix of `T_Co` -/

/-- The `E₈(−2)` coordinates of `T_Co`: the eight indices `3, …, 10`. -/
def cobleE8Index (j : Fin 8) : Fin 11 :=
  ⟨j.val + 3, by omega⟩

@[simp] theorem cobleE8Index_val (j : Fin 8) : (cobleE8Index j).val = j.val + 3 := rfl

/-- The `E₈(−2)` block of the Gram matrix of `T_Co`. -/
noncomputable def cobleE8Block : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j => cobleGramMatrix (cobleE8Index i) (cobleE8Index j)

/-- The `E₈(−2)` block is twice the negative `E₈` form. -/
theorem cobleE8Block_eq : cobleE8Block = (2 : ℤ) • e8GramMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [cobleE8Block, cobleE8Index, cobleGramMatrix, e8GramMatrix_eq, Matrix.smul_apply]
      <;> decide)

/-- The real `E₈(−2)` block, written as a negative Gram matrix `-(Bᵀ * B)` of an invertible real
change of basis. -/
noncomputable def cobleE8RealChange : Matrix (Fin 8) (Fin 8) ℝ :=
  Real.sqrt 2 • e8RealRootChange

theorem e8RealRootChange_mulVec_injective :
    Function.Injective e8RealRootChange.mulVec := by
  intro x y h
  have h' := congrArg (fun z => e8RealRootChangeInverse.mulVec z) h
  simpa [Matrix.mulVec_mulVec, e8RealRootChange_leftInverse, Matrix.one_mulVec] using h'

theorem cobleE8RealChange_mulVec_injective :
    Function.Injective cobleE8RealChange.mulVec := by
  have hsq : Real.sqrt 2 ≠ 0 := by
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact ne_of_gt hpos
  intro x y h
  have h3 : Real.sqrt 2 • e8RealRootChange.mulVec x = Real.sqrt 2 • e8RealRootChange.mulVec y := by
    simpa [cobleE8RealChange, Matrix.smul_mulVec] using h
  exact e8RealRootChange_mulVec_injective (smul_right_injective (Fin 8 → ℝ) hsq h3)

/-- The real `E₈(−2)` block is the negative Gram matrix of the invertible change
`cobleE8RealChange`. -/
theorem cobleE8Block_map_eq :
    cobleE8Block.map (Int.castRingHom ℝ) =
      -(cobleE8RealChange.transpose * cobleE8RealChange) := by
  have hmap : cobleE8Block.map (Int.castRingHom ℝ) =
      (2 : ℝ) • (e8GramMatrix.map (Int.castRingHom ℝ)) := by
    rw [cobleE8Block_eq]
    ext i j
    change (((2 : ℤ) * e8GramMatrix i j : ℤ) : ℝ) = (2 : ℝ) * ((e8GramMatrix i j : ℤ) : ℝ)
    rw [Int.cast_mul]
    norm_num
  rw [hmap, e8RealGram_factorization, cobleE8RealChange, Matrix.transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), smul_neg]

/-- **The `E₈(−2)` block is negative definite of rank eight.** -/
theorem cobleE8Block_matrixSignature :
    matrixSignature ℝ (cobleE8Block.map (Int.castRingHom ℝ)) = (0, 8, 0) := by
  rw [cobleE8Block_map_eq]
  exact matrixSignature_neg_transpose_mul_self _ cobleE8RealChange_mulVec_injective

end LeanCategories.Lattices.Valued

namespace LeanCategories.Lattices.Valued

/-! ## The nine surviving coordinates of `T_Co` -/

/-- The coordinate index of `Q = e^⊥/e`: the `⟨2⟩` vector and the eight `E₈(−2)` vectors. -/
def cobleQIndex : Fin 1 ⊕ Fin 8 → Fin 11
  | Sum.inl _ => 0
  | Sum.inr j => cobleE8Index j

@[simp] theorem cobleQIndex_inl (k : Fin 1) : cobleQIndex (Sum.inl k) = 0 := rfl

@[simp] theorem cobleQIndex_inr (j : Fin 8) : cobleQIndex (Sum.inr j) = cobleE8Index j := rfl

theorem cobleQIndex_ne_one (k : Fin 1 ⊕ Fin 8) : cobleQIndex k ≠ 1 := by
  rcases k with k | j
  · rw [cobleQIndex_inl]
    decide
  · rw [cobleQIndex_inr]
    intro h
    have h1 := congrArg Fin.val h
    simp [cobleE8Index] at h1

theorem cobleQIndex_ne_two (k : Fin 1 ⊕ Fin 8) : cobleQIndex k ≠ 2 := by
  rcases k with k | j
  · rw [cobleQIndex_inl]
    decide
  · rw [cobleQIndex_inr]
    intro h
    have h1 := congrArg Fin.val h
    simp [cobleE8Index] at h1

theorem cobleQIndex_injective : Function.Injective cobleQIndex := by
  rintro (k | j) (k' | j') h
  · rw [Subsingleton.elim k k']
  · rw [cobleQIndex_inl, cobleQIndex_inr] at h
    have h1 := congrArg Fin.val h
    simp [cobleE8Index] at h1
  · rw [cobleQIndex_inr, cobleQIndex_inl] at h
    have h1 := congrArg Fin.val h
    simp [cobleE8Index] at h1
  · rw [cobleQIndex_inr, cobleQIndex_inr] at h
    have h1 := congrArg Fin.val h
    simp only [cobleE8Index] at h1
    rw [Fin.ext (by omega : j.val = j'.val)]

/-- Every index of `T_Co` other than the two `U(2)` coordinates is a surviving one. -/
theorem cobleQIndex_eq_two_or_range {j : Fin 11} (hj : j ≠ 1) :
    j = 2 ∨ ∃ k : Fin 1 ⊕ Fin 8, cobleQIndex k = j := by
  rcases Nat.lt_or_ge j.val 2 with h | h
  · interval_cases h0 : j.val
    · exact Or.inr ⟨Sum.inl 0, Fin.ext (by simpa [cobleQIndex] using h0.symm)⟩
    · exact absurd (Fin.ext (by simpa using h0)) hj
  · rcases Nat.eq_or_lt_of_le h with h2 | h3
    · exact Or.inl (Fin.ext (by simpa using h2.symm))
    · refine Or.inr ⟨Sum.inr ⟨j.val - 3, by omega⟩, Fin.ext ?_⟩
      simp only [cobleQIndex_inr, cobleE8Index]
      omega

set_option backward.isDefEq.respectTransparency false in
/-- The representative of `Q` at each surviving coordinate: the corresponding basis vector of
`T_Co`, which lies in the hyperplane `x₂ = 0`. -/
noncomputable def cobleQVec (k : Fin 1 ⊕ Fin 8) : ↥cobleReductionData.perp :=
  ⟨(Pi.basisFun ℤ (Fin 11) (cobleQIndex k) : ↥cobleLattice.obj.carrier), by
    refine (coble_mem_perp_iff _).mpr ?_
    rw [cobleCoordFun_apply, Pi.basisFun_apply,
      Pi.single_eq_of_ne (Ne.symm (cobleQIndex_ne_two k))]⟩

@[simp] theorem cobleQVec_coe (k : Fin 1 ⊕ Fin 8) :
    ((cobleQVec k : ↥cobleReductionData.perp) : ↥cobleLattice.obj.carrier) =
      (Pi.basisFun ℤ (Fin 11) (cobleQIndex k) : ↥cobleLattice.obj.carrier) := rfl

theorem cobleCoordFun_qVec (k : Fin 1 ⊕ Fin 8) (i : Fin 11) :
    cobleCoordFun i ((cobleQVec k : ↥cobleReductionData.perp) : ↥cobleLattice.obj.carrier) =
      if i = cobleQIndex k then 1 else 0 := by
  rw [cobleCoordFun_apply, cobleQVec_coe, Pi.basisFun_apply, Pi.single_apply]

/-- Coordinates on `P^⊥`, read off the nine surviving coordinates of `T_Co`. -/
noncomputable def coblePerpCoords :
    ↥cobleReductionData.perp →ₗ[ℤ] (Fin 1 ⊕ Fin 8 → ℤ) where
  toFun x k := cobleCoordFun (cobleQIndex k) (x : ↥cobleLattice.obj.carrier)
  map_add' x y := by
    funext k
    simp
  map_smul' a x := by
    funext k
    simp

@[simp] theorem coblePerpCoords_apply (x : ↥cobleReductionData.perp) (k : Fin 1 ⊕ Fin 8) :
    coblePerpCoords x k =
      cobleCoordFun (cobleQIndex k) (x : ↥cobleLattice.obj.carrier) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The coordinates vanish on the isotropic line, so they descend to the reduction. -/
theorem coblePerpCoords_eq_zero_of_mem_kernel {x : ↥cobleReductionData.perp}
    (hx : x ∈ cobleReductionData.kernel) : coblePerpCoords x = 0 := by
  rw [IsotropicReductionData.mem_kernel_iff] at hx
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
  funext k
  rw [coblePerpCoords_apply, Pi.zero_apply]
  conv_lhs => rw [show ((x : ↥cobleReductionData.perp) : ↥cobleLattice.obj.carrier) =
    a • coblePlaneV from ha.symm]
  rw [map_smul, smul_eq_mul, cobleCoordFun_apply, coblePlaneV, cobleVectorCoord_apply,
    if_neg (cobleQIndex_ne_one k), mul_zero]

/-- The coordinate map on `Q = e^⊥/e`. -/
noncomputable def cobleQCoords :
    cobleReduction.carrier →ₗ[ℤ] (Fin 1 ⊕ Fin 8 → ℤ) :=
  cobleReductionData.kernel.liftQ coblePerpCoords fun _ hy =>
    coblePerpCoords_eq_zero_of_mem_kernel hy

@[simp] theorem cobleQCoords_mk (x : ↥cobleReductionData.perp) :
    cobleQCoords (Submodule.Quotient.mk x) = coblePerpCoords x := rfl

/-- The sum of the representatives picked out by a coordinate vector. -/
noncomputable def cobleQSum (z : Fin 1 ⊕ Fin 8 → ℤ) : ↥cobleReductionData.perp :=
  ⟨∑ k, z k • ((cobleQVec k : ↥cobleReductionData.perp) : ↥cobleLattice.obj.carrier),
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (cobleQVec k).2⟩

@[simp] theorem cobleQSum_coe (z : Fin 1 ⊕ Fin 8 → ℤ) :
    ((cobleQSum z : ↥cobleReductionData.perp) : ↥cobleLattice.obj.carrier) =
      ∑ k, z k • ((cobleQVec k : ↥cobleReductionData.perp) : ↥cobleLattice.obj.carrier) := rfl

/-- The class of a coordinate vector, as an element of `Q`. -/
noncomputable def cobleQClass (z : Fin 1 ⊕ Fin 8 → ℤ) : cobleReduction.carrier :=
  Submodule.Quotient.mk (cobleQSum z)

set_option backward.isDefEq.respectTransparency false in
/-- The sum of the representatives picked out by a coordinate vector, as a linear map. -/
noncomputable def cobleQSumHom : (Fin 1 ⊕ Fin 8 → ℤ) →ₗ[ℤ] ↥cobleReductionData.perp where
  toFun := cobleQSum
  map_add' z w := by
    apply Subtype.ext
    simp only [Submodule.coe_add, cobleQSum_coe, Pi.add_apply, add_smul,
      Finset.sum_add_distrib]
  map_smul' a z := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, cobleQSum_coe, Pi.smul_apply, smul_eq_mul, Finset.smul_sum,
      smul_smul, RingHom.id_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The class map is linear. -/
noncomputable def cobleQClassHom : (Fin 1 ⊕ Fin 8 → ℤ) →ₗ[ℤ] cobleReduction.carrier :=
  cobleReductionData.kernel.mkQ.comp cobleQSumHom

theorem cobleQClassHom_apply (z : Fin 1 ⊕ Fin 8 → ℤ) :
    cobleQClassHom z = cobleQClass z := by
  show cobleReductionData.kernel.mkQ (cobleQSum z) = Submodule.Quotient.mk (cobleQSum z)
  exact Submodule.mkQ_apply _ _

set_option backward.isDefEq.respectTransparency false in
theorem cobleQCoords_class (z : Fin 1 ⊕ Fin 8 → ℤ) : cobleQCoords (cobleQClass z) = z := by
  funext k
  rw [cobleQClass, cobleQCoords_mk, coblePerpCoords_apply, cobleQSum_coe, map_sum]
  rw [Finset.sum_eq_single k]
  · rw [map_smul, smul_eq_mul, cobleCoordFun_qVec, if_pos rfl, mul_one]
  · intro l _ hl
    rw [map_smul, smul_eq_mul, cobleCoordFun_qVec,
      if_neg (fun h => hl (cobleQIndex_injective h).symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

set_option backward.isDefEq.respectTransparency false in
/-- Every vector of `T_Co` is the sum of its coordinates in the standard basis. -/
theorem coble_eq_sum_basis (x : ↥cobleLattice.obj.carrier) :
    x = ∑ i, cobleCoordFun i x •
      (Pi.basisFun ℤ (Fin 11) i : ↥cobleLattice.obj.carrier) := by
  conv_lhs => rw [← (Pi.basisFun ℤ (Fin 11)).sum_equivFun x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cobleCoordFun_apply,
    show (Pi.basisFun ℤ (Fin 11)).equivFun x i = (x : Fin 11 → ℤ) i from by
      rw [← cobleCoordEquiv]
      exact congrFun (cobleCoordEquiv_apply x) i]

set_option backward.isDefEq.respectTransparency false in
/-- A vector with all coordinates off a single index is a multiple of that basis vector. -/
theorem coble_eq_smul_basis_of_coord_eq_zero (y : ↥cobleLattice.obj.carrier) {i : Fin 11}
    (h : ∀ j, j ≠ i → cobleCoordFun j y = 0) :
    y = cobleCoordFun i y •
      (Pi.basisFun ℤ (Fin 11) i : ↥cobleLattice.obj.carrier) := by
  conv_lhs => rw [coble_eq_sum_basis y]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [h j hj, zero_smul])
    (fun hj => absurd (Finset.mem_univ i) hj)]

set_option backward.isDefEq.respectTransparency false in
/-- The isotropic vector is the first standard basis vector. -/
theorem coblePlaneV_eq_basis_one :
    coblePlaneV = (Pi.basisFun ℤ (Fin 11) 1 : ↥cobleLattice.obj.carrier) := by
  funext i
  rw [coblePlaneV, cobleVectorCoord_apply, Pi.basisFun_apply, Pi.single_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The difference between a vector of `P^⊥` and the reconstruction of its surviving coordinates
vanishes off the isotropic coordinate. -/
theorem cobleQCoord_vanish {x : ↥cobleReductionData.perp} {j : Fin 11} (hj : j ≠ 1) :
    cobleCoordFun j (((x : ↥cobleReductionData.perp) : ↥cobleLattice.obj.carrier) -
      ∑ k : Fin 1 ⊕ Fin 8, coblePerpCoords x k •
        ((cobleQVec k : ↥cobleReductionData.perp) : ↥cobleLattice.obj.carrier)) = 0 := by
  have hsum : ∀ k : Fin 1 ⊕ Fin 8,
      cobleCoordFun j (coblePerpCoords x k •
        ((cobleQVec k : ↥cobleReductionData.perp) : ↥cobleLattice.obj.carrier)) =
      coblePerpCoords x k * (if j = cobleQIndex k then 1 else 0) := by
    intro k
    rw [map_smul, smul_eq_mul, cobleCoordFun_qVec]
  rw [map_sub, map_sum, Finset.sum_congr rfl fun k _ => hsum k]
  rcases cobleQIndex_eq_two_or_range hj with h2 | ⟨k₀, hk₀⟩
  · subst h2
    rw [(coble_mem_perp_iff _).mp x.2, Finset.sum_eq_zero, sub_zero]
    intro k _
    rw [if_neg (fun h => cobleQIndex_ne_two k h.symm), mul_zero]
  · rw [← hk₀, Finset.sum_eq_single k₀]
    · rw [if_pos rfl, mul_one, coblePerpCoords_apply, sub_self]
    · intro l _ hl
      rw [if_neg (fun h => hl (cobleQIndex_injective h).symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ k₀) h

set_option backward.isDefEq.respectTransparency false in
theorem cobleQClass_coords (q : cobleReduction.carrier) :
    cobleQClass (cobleQCoords q) = q := by
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
    rw [cobleQClass, cobleQCoords_mk]
    have hy : ((x : ↥cobleReductionData.perp) : ↥cobleLattice.obj.carrier) -
        ∑ k : Fin 1 ⊕ Fin 8, coblePerpCoords x k •
          ((cobleQVec k : ↥cobleReductionData.perp) : ↥cobleLattice.obj.carrier) =
        cobleCoordFun 1 (((x : ↥cobleReductionData.perp) : ↥cobleLattice.obj.carrier) -
          ∑ k : Fin 1 ⊕ Fin 8, coblePerpCoords x k •
            ((cobleQVec k : ↥cobleReductionData.perp) : ↥cobleLattice.obj.carrier)) •
          (Pi.basisFun ℤ (Fin 11) 1 : ↥cobleLattice.obj.carrier) :=
      coble_eq_smul_basis_of_coord_eq_zero _ fun j hj => cobleQCoord_vanish hj
    have hmem : ((x : ↥cobleReductionData.perp) : ↥cobleLattice.obj.carrier) -
        ∑ k : Fin 1 ⊕ Fin 8, coblePerpCoords x k •
          ((cobleQVec k : ↥cobleReductionData.perp) : ↥cobleLattice.obj.carrier) ∈
        cobleReductionData.submodule := by
      rw [hy, ← coblePlaneV_eq_basis_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    refine (Submodule.Quotient.eq _).mpr ?_
    have hval : (((cobleQSum (coblePerpCoords x) - x : ↥cobleReductionData.perp) :
        ↥cobleLattice.obj.carrier)) = -(((x : ↥cobleReductionData.perp) :
          ↥cobleLattice.obj.carrier) -
        ∑ k : Fin 1 ⊕ Fin 8, coblePerpCoords x k •
          ((cobleQVec k : ↥cobleReductionData.perp) : ↥cobleLattice.obj.carrier)) := by
      rw [Submodule.coe_sub, cobleQSum_coe]
      abel
    have hmem' : (((cobleQSum (coblePerpCoords x) - x : ↥cobleReductionData.perp) :
        ↥cobleLattice.obj.carrier)) ∈ cobleReductionData.submodule := by
      rw [hval]
      exact Submodule.neg_mem _ hmem
    exact hmem'

theorem cobleQCoords_comp_classHom : cobleQCoords.comp cobleQClassHom = LinearMap.id :=
  LinearMap.ext fun z => by
    rw [LinearMap.comp_apply, LinearMap.id_apply, cobleQClassHom_apply]
    exact cobleQCoords_class z

theorem cobleQClassHom_comp_coords : cobleQClassHom.comp cobleQCoords = LinearMap.id :=
  LinearMap.ext fun q => by
    rw [LinearMap.comp_apply, LinearMap.id_apply, cobleQClassHom_apply]
    exact cobleQClass_coords q

/-- The coordinate equivalence `Q ≃ₗ[ℤ] (Fin 1 ⊕ Fin 8 → ℤ)`. -/
noncomputable def cobleQCoordEquiv :
    cobleReduction.carrier ≃ₗ[ℤ] (Fin 1 ⊕ Fin 8 → ℤ) :=
  LinearEquiv.ofLinearMap cobleQCoords cobleQClassHom cobleQCoords_comp_classHom
    cobleQClassHom_comp_coords

@[simp] theorem cobleQCoordEquiv_apply_mk (x : ↥cobleReductionData.perp) :
    cobleQCoordEquiv (Submodule.Quotient.mk x) = coblePerpCoords x := rfl

theorem cobleQCoordEquiv_symm_apply (z : Fin 1 ⊕ Fin 8 → ℤ) :
    cobleQCoordEquiv.symm z = cobleQClass z := by
  apply cobleQCoordEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  exact (cobleQCoords_class z).symm

/-- **The nine classes of `e₀, e₃, …, e₁₀` are a `ℤ`-basis of `Q = e^⊥/e`.** -/
noncomputable def cobleReductionBasis :
    Module.Basis (Fin 1 ⊕ Fin 8) ℤ cobleReduction.carrier :=
  (Pi.basisFun ℤ (Fin 1 ⊕ Fin 8)).map cobleQCoordEquiv.symm

set_option backward.isDefEq.respectTransparency false in
theorem cobleReductionBasis_apply (k : Fin 1 ⊕ Fin 8) :
    cobleReductionBasis k =
      (Submodule.Quotient.mk (cobleQVec k) : cobleReduction.carrier) := by
  rw [cobleReductionBasis, Module.Basis.map_apply, Pi.basisFun_apply,
    cobleQCoordEquiv_symm_apply, cobleQClass]
  congr 1
  apply Subtype.ext
  rw [cobleQSum_coe, Finset.sum_eq_single k]
  · rw [Pi.single_eq_same, one_smul]
  · intro l _ hl
    rw [Pi.single_apply, if_neg hl, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ k) h

set_option backward.isDefEq.respectTransparency false in
/-- The pairing of two basis classes of `Q` is the corresponding Gram entry of `T_Co`. -/
theorem cobleReductionBasis_pairing (k l : Fin 1 ⊕ Fin 8) :
    (cobleReductionData.reductionLattice coble_isSymmetric).obj.pairing
        (cobleReductionBasis k) (cobleReductionBasis l) =
      cobleGramMatrix (cobleQIndex k) (cobleQIndex l) := by
  rw [cobleReductionBasis_apply, cobleReductionBasis_apply,
    IsotropicReductionData.reductionLattice_pairing_mk, cobleQVec_coe, cobleQVec_coe,
    coble_pairing_basis]

/-- The first row of the Gram matrix of `T_Co` vanishes off the first coordinate. -/
theorem cobleGramMatrix_zero_right (j : Fin 11) (hj : j ≠ 0) : cobleGramMatrix 0 j = 0 := by
  fin_cases j
  · exact absurd rfl hj
  all_goals (simp only [cobleGramMatrix]; decide)

/-- The first column of the Gram matrix of `T_Co` vanishes off the first coordinate. -/
theorem cobleGramMatrix_zero_left (j : Fin 11) (hj : j ≠ 0) : cobleGramMatrix j 0 = 0 := by
  fin_cases j
  · exact absurd rfl hj
  all_goals (simp only [cobleGramMatrix]; decide)

set_option backward.isDefEq.respectTransparency false in
/-- The entries of the block sum of the `⟨2⟩` and `E₈(−2)` blocks. -/
theorem cobleGramMatrix_block (k l : Fin 1 ⊕ Fin 8) :
    cobleGramMatrix (cobleQIndex k) (cobleQIndex l) =
      matrixBlockSum (!![2] : Matrix (Fin 1) (Fin 1) ℤ) cobleE8Block k l := by
  rcases k with k | j <;> rcases l with k' | j'
  · obtain rfl : k = 0 := Subsingleton.elim _ _
    obtain rfl : k' = 0 := Subsingleton.elim _ _
    simp only [cobleQIndex_inl, cobleGramMatrix, matrixBlockSum, Matrix.fromBlocks_apply₁₁]
    decide
  · obtain rfl : k = 0 := Subsingleton.elim _ _
    simp only [cobleQIndex_inl, cobleQIndex_inr, matrixBlockSum, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply]
    rw [cobleGramMatrix_zero_right _ (fun hc => by
      have := congrArg Fin.val hc
      simp [cobleE8Index] at this)]
  · obtain rfl : k' = 0 := Subsingleton.elim _ _
    simp only [cobleQIndex_inl, cobleQIndex_inr, matrixBlockSum, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]
    rw [cobleGramMatrix_zero_left _ (fun hc => by
      have := congrArg Fin.val hc
      simp [cobleE8Index] at this)]
  · simp only [cobleQIndex_inr, cobleGramMatrix, cobleE8Block, matrixBlockSum,
      Matrix.fromBlocks_apply₂₂]

set_option backward.isDefEq.respectTransparency false in
/-- **The Gram matrix of `Q` in the basis of the surviving coordinates is `⟨2⟩ ⊕ E₈(−2)`.** -/
theorem cobleReduction_gramMatrix :
    gramMatrix (cobleReductionData.reductionLattice coble_isSymmetric) cobleReductionBasis =
      matrixBlockSum (!![2] : Matrix (Fin 1) (Fin 1) ℤ) cobleE8Block := by
  ext k l
  rw [gramMatrix, LinearMap.BilinForm.toMatrix_apply]
  exact (cobleReductionBasis_pairing k l).trans (cobleGramMatrix_block k l)

/-! ## The signature of `Q` -/

/-- The `1 × 1` block `⟨2⟩` is the quadratic form `x ↦ 2 x₀²`. -/
theorem cobleOneBlock_quadraticForm :
    matrixQuadraticForm ℝ ((!![2] : Matrix (Fin 1) (Fin 1) ℤ).map (Int.castRingHom ℝ)) =
      QuadraticMap.weightedSumSquares ℝ fun _ : Fin 1 => (2 : ℝ) := by
  ext x
  have hmat : (![![(2 : ℤ)]] : Fin 1 → Fin 1 → ℤ) 0 0 = 2 := rfl
  simp only [matrixQuadraticForm, LinearMap.BilinMap.toQuadraticMap_apply,
    QuadraticMap.weightedSumSquares_apply, Matrix.toBilin'_apply', Matrix.map_apply,
    Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_one, smul_eq_mul, hmat]
  have hc : (Int.castRingHom ℝ) (2 : ℤ) = (2 : ℝ) := by norm_num
  rw [hc]
  ring

/-- The `1 × 1` block `⟨2⟩` contributes one positive square. -/
theorem cobleOneBlock_matrixSignature :
    matrixSignature ℝ ((!![2] : Matrix (Fin 1) (Fin 1) ℤ).map (Int.castRingHom ℝ)) =
      (1, 0, 0) := by
  rw [matrixSignature_eq_of_equivalent_weighted ℝ _ (fun _ : Fin 1 => (2 : ℝ)) (by
    rw [cobleOneBlock_quadraticForm]
    exact QuadraticMap.Equivalent.refl _)]
  have hpos : {i : Fin 1 | (0 : ℝ) < 2} = Set.univ := by
    ext i
    simp
  have hneg : {i : Fin 1 | (2 : ℝ) < 0} = ∅ := by
    ext i
    simp
  have hzero : {i : Fin 1 | (2 : ℝ) = 0} = ∅ := by
    ext i
    simp
  rw [hpos, hneg, hzero]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- **The real signature of `Q = e^⊥/e` is `(1, 8, 0)`**: one positive square from the `⟨2⟩` summand
and eight negative ones from `E₈(−2)`. -/
theorem cobleReduction_matrixSignature :
    matrixSignature ℝ ((gramMatrix (cobleReductionData.reductionLattice coble_isSymmetric)
      cobleReductionBasis).map (Int.castRingHom ℝ)) = (1, 8, 0) := by
  rw [cobleReduction_gramMatrix]
  have hmap : (matrixBlockSum (!![2] : Matrix (Fin 1) (Fin 1) ℤ) cobleE8Block).map
        (Int.castRingHom ℝ) =
      matrixBlockSum ((!![2] : Matrix (Fin 1) (Fin 1) ℤ).map (Int.castRingHom ℝ))
        (cobleE8Block.map (Int.castRingHom ℝ)) := by
    ext (k | k) (l | l) <;>
      simp [matrixBlockSum, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply]
  rw [hmap, matrixSignature_blockSum, cobleOneBlock_matrixSignature,
    cobleE8Block_matrixSignature]
  norm_num

/-- The reduction `Q = e^⊥/e` of `T_Co` as a finite projective integral lattice. -/
noncomputable def cobleReductionFiniteLattice : FiniteProjectiveLatticeCat ℤ ℤ where
  obj := cobleReductionData.reductionLattice coble_isSymmetric
  property := cobleReductionData.reductionLattice_finite coble_isSymmetric

set_option backward.isDefEq.respectTransparency false in
/-- **The signature of the reduction `Q = e^⊥/e` of `T_Co` is `(1, 8)`.** -/
theorem cobleReduction_integralSignature :
    integralSignature cobleReductionFiniteLattice = (1, 8, 0) := by
  rw [integralSignature_eq_matrixSignature cobleReductionFiniteLattice cobleReductionBasis]
  exact cobleReduction_matrixSignature

end LeanCategories.Lattices.Valued

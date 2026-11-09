/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CobleCusps
public import LeanCategories.Lattices.Valued.IsotropicReduction
public import LeanCategories.Lattices.Valued.EvenReduction

/-!
# The rank-one isotropic reduction of `T_Co` at the cusp `v = e₁` (#114)

For a primitive isotropic vector `e` of `T_Co`, the quotient `Q = e^⊥/e` is the hyperbolic lattice
of signature `(1, 8)` whose reflection group and chambers stage 2 uses (`#36`, `#23`). This file
instantiates the general isotropic reduction at the Coble vector `v = e₁` (`cobleVectorCoord`): the
line `ℤ v`, its reduction data, and the reduced formed module `Q = e^⊥/e`.

Nondegeneracy of `T_Co` is derived from its invertible Gram matrix
(`cobleGramMatrix_det_ne_zero`): a vector pairing to zero against everything is orthogonal to every
standard basis vector, so its coordinates solve `x ᵥ* G = 0`, whence `x = 0`.

The rank is computed here. The third row of the Gram matrix of `T_Co` is `2` at the third
coordinate and zero elsewhere (`coble_pairing_planeV`), so `e^⊥` is the kernel of the third
coordinate functional (`coble_perp_eq_ker`) and has rank `11 - 1 = 10`
(`coble_perp_finrank`); the isotropic line and the kernel of the reduction have rank one
(`coble_submodule_finrank`, `coble_kernel_finrank`); additivity of the rank over the quotient
gives `Module.finrank ℤ Q.carrier = 9` (`cobleReduction_finrank`).

The **signature** `(1, 8)` of `Q` is not proved here. It needs either the identification of `Q`
with `⟨2⟩ ⊕ E₈(−2)` (the `U(2)` summand reduces to nothing, and the `⟨2⟩` summand survives), or
the real signature of `T_Co` computed from its block-diagonal Gram matrix together with the
hyperbolic plane spanned by `e` and a vector pairing to `2` against it; neither is in the tree.
-/

@[expose] public section

open Matrix
open LeanCategories.Modules.Bilinear.Valued

-- The reduced carrier is a quotient of a submodule of the carrier of `T_Co`. Instance synthesis
-- can pick different but equal module structures on that nested carrier; pinning the two quotient
-- and submodule structures keeps the finrank arithmetic below on one structure.
attribute [local instance 10000] Submodule.module
attribute [local instance 10000] Submodule.Quotient.module

namespace LeanCategories.Lattices.Valued




theorem cobleGramMatrix_det_ne_zero : cobleGramMatrix.det ≠ 0 := by
  rw [cobleGramMatrix_eq, Matrix.det_smul, Fintype.card_fin]
  exact mul_ne_zero (pow_ne_zero 11 (by norm_num)) cobleHalfMatrix_det_ne_zero

theorem coble_isSymmetric : cobleLattice.obj.IsSymmetric := by
  intro x y
  have hxy : cobleLattice.obj.pairing x y =
      ∑ i, ∑ j, (x : Fin 11 → ℤ) i * cobleGramMatrix i j * (y : Fin 11 → ℤ) j :=
    coble_pairing_coord _ _
  have hyx : cobleLattice.obj.pairing y x =
      ∑ i, ∑ j, (y : Fin 11 → ℤ) i * cobleGramMatrix i j * (x : Fin 11 → ℤ) j :=
    coble_pairing_coord _ _
  have hs : ∀ i j : Fin 11, cobleGramMatrix j i = cobleGramMatrix i j :=
    fun i j => (congrFun (congrFun cobleGramMatrix_isSymm j) i).symm
  rw [hxy, hyx, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hs i j]
  ring

theorem coble_leftSeparating {x : cobleLattice.obj.carrier}
    (hx : ∀ y, cobleLattice.obj.pairing x y = 0) : x = 0 := by
  have hrow : ∀ j : Fin 11, ∑ i, (x : Fin 11 → ℤ) i * cobleGramMatrix i j = 0 := by
    intro j
    have h := hx (Pi.basisFun ℤ (Fin 11) j)
    have h' : ∑ a, ∑ b, (x : Fin 11 → ℤ) a * cobleGramMatrix a b *
        ((Pi.basisFun ℤ (Fin 11) j : Fin 11 → ℤ)) b = 0 := by
      rw [← coble_pairing_coord (x := (x : Fin 11 → ℤ))
        (y := ((Pi.basisFun ℤ (Fin 11) j : Fin 11 → ℤ)))]
      exact h
    have hinner : ∀ a : Fin 11, ∑ b, (x : Fin 11 → ℤ) a * cobleGramMatrix a b *
        ((Pi.basisFun ℤ (Fin 11) j : Fin 11 → ℤ)) b
        = (x : Fin 11 → ℤ) a * cobleGramMatrix a j := by
      intro a
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Pi.basisFun_apply, hb]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [Finset.sum_congr rfl fun a _ => hinner a] at h'
    simpa using h'
  have hvec : (x : Fin 11 → ℤ) ᵥ* cobleGramMatrix = 0 := by
    funext j
    simpa only [Matrix.vecMul, dotProduct, Pi.zero_apply] using hrow j
  exact Matrix.eq_zero_of_vecMul_eq_zero cobleGramMatrix_det_ne_zero hvec

theorem coble_isNondegenerate : cobleLattice.obj.IsNondegenerate := by
  refine ⟨fun x hx => coble_leftSeparating fun y => ?_, fun y hy => ?_⟩
  · simpa only [BilinModuleCat.bilinMap_apply] using hx y
  · refine coble_leftSeparating fun x => ?_
    rw [coble_isSymmetric y x]
    simpa only [BilinModuleCat.bilinMap_apply] using hy x

/-- The primitive isotropic line `ℤ e₁` of `T_Co`. -/
noncomputable def cobleIsotropicLine : Submodule ℤ cobleLattice.obj.carrier :=
  Submodule.span ℤ {coblePlaneV}

theorem cobleIsotropicLine_isotropic :
    cobleLattice.obj.IsTotallyIsotropic cobleIsotropicLine := by
  intro x hx y hy
  rw [cobleIsotropicLine, Submodule.mem_span_singleton] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hv : cobleLattice.obj.pairing coblePlaneV coblePlaneV = 0 := cobleVector.isotropic
  rw [BilinModuleCat.pairing_smul_left, BilinModuleCat.pairing_smul_right, hv, smul_zero,
    smul_zero]

/-- The reduction data of `T_Co` at the primitive isotropic line `ℤ e₁`. -/
noncomputable def cobleReductionData : IsotropicReductionData cobleLattice where
  submodule := cobleIsotropicLine
  isotropic := cobleIsotropicLine_isotropic
  primitive := coblePlaneV_primitiveSpan
  nondegenerate := coble_isNondegenerate
  finite := cobleCarrierFinite

/-- The reduction `Q = e^⊥/e` of `T_Co` at the cusp `v = e₁`. -/
noncomputable def cobleReduction : BilinModuleCat ℤ ℤ :=
  cobleReductionData.reduction coble_isSymmetric

theorem cobleReduction_isNondegenerate : cobleReduction.IsNondegenerate :=
  cobleReductionData.reduction_isNondegenerate coble_isSymmetric

/-! ## The rank of the reduction -/

/-- The second row of the Gram matrix of `T_Co` is `2` at the third coordinate and zero elsewhere,
so the coordinate form of the pairing with the Coble vector is twice the third coordinate. -/
theorem coble_coord_sum_planeV (x : Fin 11 → ℤ) :
    ∑ i, ∑ j, cobleVectorCoord i * cobleGramMatrix i j * x j = 2 * x 2 := by
  have hrow : ∀ j : Fin 11, cobleGramMatrix 1 j = if j = 2 then 2 else 0 := by
    intro j
    fin_cases j <;> decide
  rw [Finset.sum_eq_single (1 : Fin 11)]
  · rw [Finset.sum_eq_single (2 : Fin 11)]
    · simp [hrow 2, cobleVectorCoord_apply]
    · intro j _ hj
      simp [hrow j, hj]
    · intro h
      exact absurd (Finset.mem_univ (2 : Fin 11)) h
  · intro i _ hi
    simp [cobleVectorCoord_apply, hi]
  · intro h
    exact absurd (Finset.mem_univ (1 : Fin 11)) h

/-- Pairing with the Coble vector is twice the third coordinate functional. -/
theorem coble_pairing_planeV (x : ↥cobleLattice.obj.carrier) :
    cobleLattice.obj.pairing coblePlaneV x = 2 * cobleCoordFun 2 x := by
  rw [cobleCoordFun_apply]
  exact (coble_pairing_coord cobleVectorCoord (x : Fin 11 → ℤ)).trans
    (coble_coord_sum_planeV (x : Fin 11 → ℤ))

/-- The orthogonal complement of the Coble vector is the kernel of the third coordinate
functional. -/
theorem coble_mem_perp_iff (x : ↥cobleLattice.obj.carrier) :
    x ∈ cobleReductionData.perp ↔ cobleCoordFun 2 x = 0 := by
  rw [IsotropicReductionData.perp, BilinModuleCat.mem_orthogonalSubmodule_iff]
  constructor
  · intro h
    have h0 := h coblePlaneV (Submodule.mem_span_singleton_self coblePlaneV)
    rw [coble_pairing_planeV] at h0
    rcases mul_eq_zero.mp h0 with h2 | h2
    · exact absurd h2 (by norm_num)
    · exact h2
  · intro hx p hp
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
    rw [BilinModuleCat.pairing_smul_left, smul_eq_mul, coble_pairing_planeV, hx, mul_zero,
      mul_zero]

/-- `P^⊥` is the kernel of the third coordinate functional. -/
theorem coble_perp_eq_ker :
    cobleReductionData.perp = LinearMap.ker (cobleCoordFun 2) :=
  Submodule.ext fun x => (coble_mem_perp_iff x).trans Iff.rfl

/-- The third coordinate functional is surjective. -/
theorem cobleCoordFun_two_surjective : Function.Surjective (cobleCoordFun (2 : Fin 11)) := by
  intro y
  refine ⟨y • (Pi.basisFun ℤ (Fin 11) 2 : ↥cobleLattice.obj.carrier), ?_⟩
  have h1 : cobleCoordFun 2 (Pi.basisFun ℤ (Fin 11) 2 : ↥cobleLattice.obj.carrier) = 1 :=
    (cobleCoordFun_apply 2 (Pi.basisFun ℤ (Fin 11) 2 : ↥cobleLattice.obj.carrier)).trans (by
      simp)
  calc cobleCoordFun 2 (y • (Pi.basisFun ℤ (Fin 11) 2 : ↥cobleLattice.obj.carrier))
      = y • cobleCoordFun 2 (Pi.basisFun ℤ (Fin 11) 2 : ↥cobleLattice.obj.carrier) :=
        map_smul _ _ _
    _ = y • (1 : ℤ) := by rw [h1]
    _ = y := by simp

/-- `P^⊥` has rank ten. -/
theorem coble_perp_finrank : Module.finrank ℤ ↥cobleReductionData.perp = 10 := by
  have hrank : Module.finrank ℤ ↥cobleLattice.obj.carrier = 11 :=
    (LinearEquiv.finrank_eq cobleCoordEquiv).trans (by
      rw [Module.finrank_fintype_fun_eq_card]
      simp)
  have hquot : Module.finrank ℤ (↥cobleLattice.obj.carrier ⧸
      LinearMap.ker (cobleCoordFun (2 : Fin 11))) = 1 :=
    (LinearEquiv.finrank_eq
      (LinearMap.quotKerEquivOfSurjective _ cobleCoordFun_two_surjective)).trans
      (Module.finrank_self ℤ)
  have h := Submodule.finrank_quotient_add_finrank
    (LinearMap.ker (cobleCoordFun (2 : Fin 11)))
  have hker : Module.finrank ℤ ↥(LinearMap.ker (cobleCoordFun (2 : Fin 11))) = 10 := by
    omega
  exact (LinearEquiv.finrank_eq (LinearEquiv.ofEq _ _ coble_perp_eq_ker)).trans hker

/-- The isotropic line has rank one. -/
theorem coble_submodule_finrank : Module.finrank ℤ ↥cobleReductionData.submodule = 1 := by
  have hinj : Function.Injective (LinearMap.toSpanSingleton ℤ ↥cobleLattice.obj.carrier
      coblePlaneV) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at ha
    exact (smul_eq_zero.mp ha).resolve_right cobleVector.nonzero
  have hrange : LinearMap.range (LinearMap.toSpanSingleton ℤ ↥cobleLattice.obj.carrier
      coblePlaneV) = cobleReductionData.submodule := by
    rw [LinearMap.range_toSpanSingleton]
    rfl
  exact (LinearEquiv.ofEq _ _ hrange).symm.finrank_eq.trans
    ((LinearEquiv.ofInjective _ hinj).symm.finrank_eq.trans (Module.finrank_self ℤ))

/-- The kernel of the reduction has rank one. -/
theorem coble_kernel_finrank : Module.finrank ℤ ↥cobleReductionData.kernel = 1 :=
  (LinearEquiv.finrank_eq
    (IsotropicReductionData.kernelEquivSubmodule cobleReductionData)).trans
    coble_submodule_finrank

/-- **The reduction `Q = e^⊥/e` of `T_Co` has rank nine.** -/
theorem cobleReduction_finrank : Module.finrank ℤ cobleReduction.carrier = 9 := by
  have h := Submodule.finrank_quotient_add_finrank cobleReductionData.kernel
  have hk : Module.finrank ℤ ↥cobleReductionData.kernel = 1 := coble_kernel_finrank
  have hp : Module.finrank ℤ ↥cobleReductionData.perp = 10 := coble_perp_finrank
  have h9 : Module.finrank ℤ
      (↥cobleReductionData.perp ⧸ cobleReductionData.kernel) = 9 := by omega
  exact h9

end LeanCategories.Lattices.Valued

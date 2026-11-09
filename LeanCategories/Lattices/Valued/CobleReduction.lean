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

The remaining obligation for this instance is the rank: `Module.finrank ℤ Q.carrier = 9`, which
needs `finrank ↥e^⊥ = 10` (the functional `⟨e, ·⟩` is nonzero, so `e^⊥` is its kernel) and
`finrank ↥(ℤ e) = 1`, together with quotient additivity. Those two rank inputs are not proved
here.
-/

@[expose] public section

open Matrix
open LeanCategories.Modules.Bilinear.Valued

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

end LeanCategories.Lattices.Valued

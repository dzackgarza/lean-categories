/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

/-!
# Base change of quadratic maps without `Invertible 2`

Mathlib's `QuadraticForm.baseChange` is built from the associated symmetric bilinear form and
needs `2` invertible; its uniqueness statement `QuadraticMap.baseChange_ext` does not. Here the
base change exists for every quadratic map `Q : M → N` over any commutative ring:

* on a free module with a basis `b`, `Q = (Q.toBilin b).toQuadraticMap` for a (non-symmetric)
  bilinear map (Mathlib, `QuadraticForm/Basis.lean`), and the base change of that bilinear map
  gives a quadratic map `(a ⊗ m) ↦ a² ⊗ Q m`;
* in general, `M` has the free cover `π : (M →₀ R) ↠ M` (a 1-truncated free resolution,
  FOUNDATIONS Def. 13.11). The base change `P` of `Q ∘ π` on `A ⊗ (M →₀ R)` is constant on the
  cosets of `ker (A ⊗ π)`, which is the image of `A ⊗ ker π` by right exactness of `A ⊗ −`: the
  polar form of `P` is the base change of the polar form of `Q ∘ π`, which vanishes against
  `ker π`, and `P` vanishes on the image of `A ⊗ ker π`. So `P` descends along the surjection
  `A ⊗ π`.

The result `QuadraticMap.baseChange' A Q` satisfies `baseChange'_tmul`; by `baseChange_ext` it is
the unique quadratic map with that property, so it does not depend on the cover.
-/

open TensorProduct LinearMap

namespace QuadraticMap

variable {R : Type*} [CommRing R]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (A : Type*) [CommRing A] [Algebra R A]

section Basis

variable {ι : Type*} [LinearOrder ι]

/-- The base change of a quadratic map on a module with a basis, through `Q.toBilin b`. -/
noncomputable def baseChangeOfBasis (Q : QuadraticMap R M N) (b : Module.Basis ι R M) :
    QuadraticMap A (A ⊗[R] M) (A ⊗[R] N) :=
  (LinearMap.BilinMap.baseChange A (Q.toBilin b)).toQuadraticMap

theorem baseChangeOfBasis_tmul (Q : QuadraticMap R M N) (b : Module.Basis ι R M) (a : A)
    (m : M) : baseChangeOfBasis A Q b (a ⊗ₜ m) = (a * a) ⊗ₜ Q m := by
  rw [baseChangeOfBasis, LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.BilinMap.baseChange_tmul, ← LinearMap.BilinMap.toQuadraticMap_apply,
    toQuadraticMap_toBilin]

/-- The polar form of the base change is the base change of the polar form. -/
theorem polar_baseChangeOfBasis_tmul (Q : QuadraticMap R M N) (b : Module.Basis ι R M)
    (a a' : A) (m m' : M) :
    polar (baseChangeOfBasis A Q b) (a ⊗ₜ m) (a' ⊗ₜ m') = (a * a') ⊗ₜ polar Q m m' := by
  rw [baseChangeOfBasis, LinearMap.BilinMap.polar_toQuadraticMap,
    LinearMap.BilinMap.baseChange_tmul, LinearMap.BilinMap.baseChange_tmul, mul_comm a' a,
    ← TensorProduct.tmul_add, ← LinearMap.BilinMap.polar_toQuadraticMap, toQuadraticMap_toBilin]

end Basis

section Descent

variable (Q : QuadraticMap R M N)

/-- The free cover `M →₀ R ↠ M`. -/
noncomputable abbrev cover : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id

theorem cover_surjective : Function.Surjective (cover (R := R) (M := M)) :=
  fun m => ⟨Finsupp.single m 1, by simp⟩

/-- The base change of `Q ∘ π` on the free cover. -/
noncomputable abbrev coverBaseChange : QuadraticMap A (A ⊗[R] (M →₀ R)) (A ⊗[R] N) :=
  letI : LinearOrder M := IsWellOrder.linearOrder WellOrderingRel
  baseChangeOfBasis A (Q.comp cover) (Finsupp.basisSingleOne)

/-- The base change of the cover, `A ⊗ π`. -/
noncomputable abbrev coverTensor : A ⊗[R] (M →₀ R) →ₗ[A] A ⊗[R] M :=
  LinearMap.baseChange A cover

theorem coverTensor_surjective : Function.Surjective (coverTensor (R := R) (M := M) A) := by
  have h := LinearMap.lTensor_surjective A (cover_surjective (R := R) (M := M))
  exact fun z => by
    obtain ⟨y, hy⟩ := h z
    exact ⟨y, by rw [← hy]; rfl⟩

/-- `ker (A ⊗ π)` is the image of `A ⊗ ker π` (right exactness of `A ⊗ −`). -/
theorem mem_range_of_coverTensor_eq_zero {k : A ⊗[R] (M →₀ R)} (hk : coverTensor A k = 0) :
    k ∈ LinearMap.range ((LinearMap.ker (cover (R := R) (M := M))).subtype.lTensor A) := by
  have hex : Function.Exact ⇑((LinearMap.ker (cover (R := R) (M := M))).subtype.lTensor A)
      ⇑((cover (R := R) (M := M)).lTensor A) :=
    lTensor_exact A (LinearMap.exact_subtype_ker_map _) (cover_surjective (R := R) (M := M))
  have hk' : (cover (R := R) (M := M)).lTensor A k = 0 := by
    rw [← LinearMap.baseChange_eq_ltensor]; exact hk
  exact (hex k).mp hk'

/-- The polar form of the cover's base change vanishes against the image of `A ⊗ ker π`. -/
theorem polar_coverBaseChange_ker (x : A ⊗[R] (M →₀ R))
    (y : A ⊗[R] LinearMap.ker (cover (R := R) (M := M))) :
    polar (coverBaseChange A Q) x
      ((LinearMap.ker (cover (R := R) (M := M))).subtype.lTensor A y) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp [polar]
  | tmul a f =>
    induction y using TensorProduct.induction_on with
    | zero => simp [polar]
    | tmul s κ =>
      have hκ : cover (R := R) (M := M) (κ : M →₀ R) = 0 := LinearMap.mem_ker.mp κ.2
      rw [LinearMap.lTensor_tmul, polar_baseChangeOfBasis_tmul]
      simp [polar, QuadraticMap.comp_apply, hκ]
    | add y₁ y₂ h₁ h₂ => rw [map_add, polar_add_right, h₁, h₂, add_zero]
  | add x₁ x₂ h₁ h₂ => rw [polar_add_left, h₁, h₂, add_zero]

/-- The cover's base change vanishes on the image of `A ⊗ ker π`. -/
theorem coverBaseChange_ker (y : A ⊗[R] LinearMap.ker (cover (R := R) (M := M))) :
    coverBaseChange A Q ((LinearMap.ker (cover (R := R) (M := M))).subtype.lTensor A y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s κ =>
    rw [LinearMap.lTensor_tmul, baseChangeOfBasis_tmul, QuadraticMap.comp_apply,
      Submodule.coe_subtype, LinearMap.mem_ker.mp κ.2, map_zero, TensorProduct.tmul_zero]
  | add y₁ y₂ h₁ h₂ =>
    rw [map_add, QuadraticMap.map_add (coverBaseChange A Q), h₁, h₂, polar_coverBaseChange_ker,
      zero_add, add_zero]

/-- The cover's base change is constant on the fibres of `A ⊗ π`. -/
theorem coverBaseChange_eq_of_coverTensor_eq {x x' : A ⊗[R] (M →₀ R)}
    (h : coverTensor A x = coverTensor A x') :
    coverBaseChange A Q x = coverBaseChange A Q x' := by
  obtain ⟨y, hy⟩ := mem_range_of_coverTensor_eq_zero A (k := x' - x) (by rw [map_sub, h, sub_self])
  have hx' : x' = x + (LinearMap.ker (cover (R := R) (M := M))).subtype.lTensor A y := by
    rw [hy, add_sub_cancel]
  rw [hx', QuadraticMap.map_add (coverBaseChange A Q), coverBaseChange_ker, polar_coverBaseChange_ker, add_zero, add_zero]

/-- Its polar form is constant on the fibres of `A ⊗ π` in each argument. -/
theorem polar_coverBaseChange_eq_of_coverTensor_eq {x x' z : A ⊗[R] (M →₀ R)}
    (h : coverTensor A x = coverTensor A x') :
    polar (coverBaseChange A Q) x z = polar (coverBaseChange A Q) x' z := by
  simp only [polar]
  rw [coverBaseChange_eq_of_coverTensor_eq A Q h,
    coverBaseChange_eq_of_coverTensor_eq A Q (x := x + z) (x' := x' + z)
      (by rw [map_add, map_add, h])]

/-- A chosen preimage under `A ⊗ π`. -/
noncomputable abbrev coverLift (z : A ⊗[R] M) : A ⊗[R] (M →₀ R) :=
  Function.surjInv (coverTensor_surjective (R := R) (M := M) A) z

theorem coverTensor_lift (z : A ⊗[R] M) : coverTensor A (coverLift A z) = z :=
  Function.surjInv_eq _ z

/-- The descended polar form, a bilinear map on `A ⊗ M`. -/
noncomputable def baseChangePolar : LinearMap.BilinMap A (A ⊗[R] M) (A ⊗[R] N) :=
  LinearMap.mk₂ A (fun z w => polar (coverBaseChange A Q) (coverLift A z) (coverLift A w))
    (fun z₁ z₂ w => by
      rw [polar_coverBaseChange_eq_of_coverTensor_eq A Q (x := coverLift A (z₁ + z₂))
        (x' := coverLift A z₁ + coverLift A z₂) (by rw [map_add, coverTensor_lift, coverTensor_lift,
          coverTensor_lift]), polar_add_left])
    (fun a z w => by
      rw [polar_coverBaseChange_eq_of_coverTensor_eq A Q (x := coverLift A (a • z))
        (x' := a • coverLift A z) (by rw [map_smul, coverTensor_lift, coverTensor_lift]),
        polar_smul_left])
    (fun z w₁ w₂ => by
      rw [polar_comm, polar_coverBaseChange_eq_of_coverTensor_eq A Q (x := coverLift A (w₁ + w₂))
        (x' := coverLift A w₁ + coverLift A w₂) (by rw [map_add, coverTensor_lift, coverTensor_lift,
          coverTensor_lift]), polar_add_left, polar_comm _ (coverLift A w₁), polar_comm _ (coverLift A w₂)])
    (fun a z w => by
      rw [polar_comm, polar_coverBaseChange_eq_of_coverTensor_eq A Q (x := coverLift A (a • w))
        (x' := a • coverLift A w) (by rw [map_smul, coverTensor_lift, coverTensor_lift]),
        polar_smul_left, polar_comm])

/-- **Base change of a quadratic map** along `R → A`, for any commutative rings and any modules:
`(a ⊗ m) ↦ a² ⊗ Q m` (`baseChange'_tmul`), with no hypothesis on `2`. -/
noncomputable def baseChange' : QuadraticMap A (A ⊗[R] M) (A ⊗[R] N) where
  toFun z := coverBaseChange A Q (coverLift A z)
  toFun_smul a z := by
    rw [coverBaseChange_eq_of_coverTensor_eq A Q (x := coverLift A (a • z)) (x' := a • coverLift A z)
      (by rw [map_smul, coverTensor_lift, coverTensor_lift]), QuadraticMap.map_smul]
  exists_companion' := ⟨baseChangePolar A Q, fun z w => by
    change coverBaseChange A Q (coverLift A (z + w)) = coverBaseChange A Q (coverLift A z) +
      coverBaseChange A Q (coverLift A w) + polar (coverBaseChange A Q) (coverLift A z) (coverLift A w)
    rw [coverBaseChange_eq_of_coverTensor_eq A Q (x := coverLift A (z + w))
      (x' := coverLift A z + coverLift A w) (by rw [map_add, coverTensor_lift, coverTensor_lift,
        coverTensor_lift]), QuadraticMap.map_add (coverBaseChange A Q)]⟩

@[simp] theorem baseChange'_tmul (a : A) (m : M) :
    baseChange' A Q (a ⊗ₜ m) = (a * a) ⊗ₜ Q m := by
  change coverBaseChange A Q (coverLift A (a ⊗ₜ m)) = _
  rw [coverBaseChange_eq_of_coverTensor_eq A Q (x := coverLift A (a ⊗ₜ m))
    (x' := a ⊗ₜ Finsupp.single m 1) (by rw [coverTensor_lift]; simp), baseChangeOfBasis_tmul,
    QuadraticMap.comp_apply]
  simp

end Descent

end QuadraticMap

/-- In characteristic `2`, where `QuadraticForm.baseChange` does not apply: the square on `ℤ`
extended to `ℤ/2` sends `a ⊗ m` to `a² ⊗ m²`. -/
example (a : ZMod 2) (m : ℤ) :
    QuadraticMap.baseChange' (ZMod 2) (QuadraticMap.sq (R := ℤ)) (a ⊗ₜ m) = (a * a) ⊗ₜ (m * m) := by
  simp

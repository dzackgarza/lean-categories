/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.IsotropicReductionRealPerp

/-!
# The quotient isometry `(e^⊥/ℤe) ⊗[ℤ] ℝ ≃ (e_ℝ)^⊥/⟨e_ℝ⟩` (#122)

For an integral `ℤ`-lattice `L`, the reduction `e^⊥/ℤe` of an isotropic vector carries the form
induced by `L` (`lineReductionForm`: the restriction of the pairing to `e^⊥`, descended to the
quotient by `LinearMap.BilinMap.liftQ₂`, the line case of `IsotropicReductionData.
reductionBilinMap`), and its base change to `ℝ` carries the real form of that induced form
(`lineReductionReal`, built from `LinearMap.BilinMap.baseChange` and
`TensorProduct.AlgebraTensorModule.rid` exactly as `realPairing` is).

**The theorem of this module (#122)** is `perpQuotientTensorEquiv`: the linear equivalence
`(e^⊥/ℤe) ⊗[ℤ] ℝ ≃ (e_ℝ)^⊥/⟨e_ℝ⟩` between the base change of the reduction and the real
quotient of `IsotropicQuotientSignature`, and `lineReductionRealIsometryEquiv`: it is an
isometry of the induced forms. The signature of `e^⊥/ℤe` is then the #119 signature of the
real quotient (`sigPos_lineReductionRealQuadratic`, `sigNeg_lineReductionRealQuadratic`).

The equivalence is the composition of the two steps the issue names:

* right exactness of `⊗`: Mathlib's `TensorProduct.AlgebraTensorModule.tensorQuotientEquiv`,
  the `lTensor` cokernel form `(M ⊗[R] (N ⧸ n)) ≃ₗ[A] (M ⊗[R] N) ⧸ range (lTensor A M
  n.subtype)`, identifies `(e^⊥/ℤe) ⊗[ℤ] ℝ` with
  `(ℝ ⊗[ℤ] e^⊥) ⧸ range (lTensor ℝ of ℤe → e^⊥)`;
* `Submodule.Quotient.equiv` transports that quotient along `perpTensorEquiv`
  (`ℝ ⊗[ℤ] e^⊥ ≃ (e_ℝ)^⊥`, #124) using `map_range_isotropicLineKernel` (#124): the range
  of `lTensor ℝ` of the inclusion `ℤe → e^⊥` is carried onto the real line `ℝ · e_ℝ`.

The objects keep their standard definitions: `L_ℝ` is the base change `ℝ ⊗[ℤ] L.obj.carrier`
(`TensorProduct ℤ ℝ _`, as `realPairing`), and each quotient is a `Submodule` quotient.

The isometry cannot be an induction on values (a quadratic form is not additive in its
argument), so it goes through the associated bilinear forms: the associated form of the
quotient computes on classes as the restriction of the real pairing
(`associated_isotropicQuotientForm_mk`, from the polar formula and `isotropicQuotientForm_mk`),
and the bilinear transport along the equivalence is proved on pure tensors and extended
additively in each argument
(`associated_isotropicQuotientForm_perpQuotientTensorEquiv`; on `r ⊗ₜ [x]` and `s ⊗ₜ [y]`
both sides are `(r * s) * (b(x, y) : ℝ)`, by `perpTensorEquiv_tmul` and `realPairing_tmul`
against `lineReductionReal_tmul_mk`). The values then agree because each is the diagonal of
its associated bilinear form (`QuadraticMap.associated_eq_self_apply`). The hyperbolic
partner `f` of the #119 setting is a lattice vector with `pairing f f = 0` and
`pairing e f = 1`; its image `toReal f` partners `toReal e` in the real form
(`realQuadratic_toReal`, `associated_realQuadratic_pair`).

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Izv. Akad.
  Nauk SSSR Ser. Mat. 43 (1979), §1: primitive isotropic vectors and the reduction `P^⊥/P`.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued
open scoped TensorProduct

namespace LeanCategories.Lattices.Valued

attribute [local instance 10000] Submodule.module
attribute [local instance 10000] Submodule.Quotient.module

variable {L : IntegralLatticeCat ℤ}

/-! ## The form induced by `L` on `e^⊥/ℤe` -/

section ReductionForm

/-- The form of the lattice restricted to `e^⊥`. -/
noncomputable def lineRestricted (e : L.obj.carrier) : BilinModuleCat ℤ ℤ :=
  L.obj.restrict (isotropicLinePerp (L := L) e)

theorem lineRestricted_pairing (e : L.obj.carrier)
    (x y : ↥(isotropicLinePerp (L := L) e)) :
    (lineRestricted (L := L) e).pairing x y =
      L.obj.pairing (x : L.obj.carrier) (y : L.obj.carrier) :=
  rfl

theorem isotropicLineKernel_le_leftRadical (e : L.obj.carrier) :
    isotropicLineKernel (L := L) e ≤ (lineRestricted (L := L) e).leftRadical := by
  intro x hx
  change (lineRestricted (L := L) e).bilinMap x = 0
  refine LinearMap.ext fun y => ?_
  obtain ⟨y, hy⟩ := y
  change L.obj.pairing (x : L.obj.carrier) y = 0
  obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp ((mem_isotropicLineKernel_iff e x).mp hx)
  have h0 : L.obj.pairing e y = 0 :=
    (BilinModuleCat.mem_orthogonalSubmodule_iff L.obj (isotropicLine (L := L) e) y).mp hy
      e (Submodule.mem_span_singleton_self e)
  rw [← hn, BilinModuleCat.pairing_smul_left, h0, smul_zero]

theorem isotropicLineKernel_le_rightRadical (hb : L.obj.IsSymmetric) (e : L.obj.carrier) :
    isotropicLineKernel (L := L) e ≤ (lineRestricted (L := L) e).rightRadical := by
  intro x hx
  change (lineRestricted (L := L) e).bilinMap.flip x = 0
  refine LinearMap.ext fun y => ?_
  obtain ⟨y, hy⟩ := y
  change L.obj.pairing y (x : L.obj.carrier) = 0
  rw [hb y (x : L.obj.carrier)]
  obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp ((mem_isotropicLineKernel_iff e x).mp hx)
  have h0 : L.obj.pairing e y = 0 :=
    (BilinModuleCat.mem_orthogonalSubmodule_iff L.obj (isotropicLine (L := L) e) y).mp hy
      e (Submodule.mem_span_singleton_self e)
  rw [← hn, BilinModuleCat.pairing_smul_left, h0, smul_zero]

/-- **The form induced by `L` on `e^⊥/ℤe`**: the restriction of the pairing to `e^⊥`,
descended to the quotient by the line `ℤe`, which lies in the radical of the restriction.
This is the line case of `IsotropicReductionData.reductionBilinMap`. -/
noncomputable def lineReductionForm (hb : L.obj.IsSymmetric) (e : L.obj.carrier) :
    LinearMap.BilinMap ℤ
      (↥(isotropicLinePerp (L := L) e) ⧸ isotropicLineKernel (L := L) e) ℤ :=
  (lineRestricted (L := L) e).bilinMap.liftQ₂ (isotropicLineKernel (L := L) e)
    (isotropicLineKernel (L := L) e) (isotropicLineKernel_le_leftRadical e)
    (isotropicLineKernel_le_rightRadical hb e)

/-- The reduction `e^⊥/ℤe` as a formed module. -/
noncomputable def lineReduction (hb : L.obj.IsSymmetric) (e : L.obj.carrier) :
    BilinModuleCat ℤ ℤ :=
  BilinModuleCat.ofBilinMap (lineReductionForm hb e)

@[simp] theorem lineReduction_pairing_mk (hb : L.obj.IsSymmetric) (e : L.obj.carrier)
    (x y : ↥(isotropicLinePerp (L := L) e)) :
    (lineReduction hb e).pairing (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      L.obj.pairing (x : L.obj.carrier) (y : L.obj.carrier) :=
  rfl

theorem lineReductionForm_mk (hb : L.obj.IsSymmetric) (e : L.obj.carrier)
    (x y : ↥(isotropicLinePerp (L := L) e)) :
    lineReductionForm hb e (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      L.obj.pairing (x : L.obj.carrier) (y : L.obj.carrier) :=
  rfl

end ReductionForm

/-! ## The real form of the reduction -/

section RealReductionForm

/-- The real form of the induced form, on `ℝ ⊗[ℤ] (e^⊥/ℤe)`: the base change of
`lineReductionForm`, as `realPairing` is the base change of `L.obj.bilinMap`. -/
noncomputable def lineReductionReal (hb : L.obj.IsSymmetric) (e : L.obj.carrier) :
    LinearMap.BilinForm ℝ
      (TensorProduct ℤ ℝ (↥(isotropicLinePerp (L := L) e) ⧸
        isotropicLineKernel (L := L) e)) :=
  LinearMap.compr₂ (LinearMap.BilinMap.baseChange ℝ (lineReductionForm hb e))
    (TensorProduct.AlgebraTensorModule.rid ℤ ℝ ℝ).toLinearMap

theorem lineReductionReal_tmul_mk (hb : L.obj.IsSymmetric) (e : L.obj.carrier)
    (r s : ℝ) (x y : ↥(isotropicLinePerp (L := L) e)) :
    lineReductionReal hb e
        (r ⊗ₜ[ℤ] (Submodule.Quotient.mk x : ↥(isotropicLinePerp (L := L) e) ⧸
          isotropicLineKernel (L := L) e))
        (s ⊗ₜ[ℤ] (Submodule.Quotient.mk y : ↥(isotropicLinePerp (L := L) e) ⧸
          isotropicLineKernel (L := L) e)) =
      (r * s) * (L.obj.pairing (x : L.obj.carrier) (y : L.obj.carrier) : ℝ) := by
  have hval : lineReductionReal hb e
        (r ⊗ₜ[ℤ] (Submodule.Quotient.mk x : ↥(isotropicLinePerp (L := L) e) ⧸
          isotropicLineKernel (L := L) e))
        (s ⊗ₜ[ℤ] (Submodule.Quotient.mk y : ↥(isotropicLinePerp (L := L) e) ⧸
          isotropicLineKernel (L := L) e)) =
      (r * s) * ((lineReductionForm hb e
        (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) : ℤ) : ℝ) := by
    simp [lineReductionReal, Algebra.smul_def, mul_comm]
  rw [hval, lineReductionForm_mk]

/-- The real quadratic form induced on `ℝ ⊗[ℤ] (e^⊥/ℤe)`: `x ↦ b(x, x)` for the real form
of the induced form. The signature of `e^⊥/ℤe` is the signature of this form. -/
noncomputable def lineReductionRealQuadratic (hb : L.obj.IsSymmetric) (e : L.obj.carrier) :
    QuadraticForm ℝ
      (TensorProduct ℤ ℝ (↥(isotropicLinePerp (L := L) e) ⧸
        isotropicLineKernel (L := L) e)) :=
  LinearMap.BilinMap.toQuadraticMap (lineReductionReal hb e)

theorem lineReductionRealQuadratic_tmul_mk (hb : L.obj.IsSymmetric) (e : L.obj.carrier)
    (r : ℝ) (x : ↥(isotropicLinePerp (L := L) e)) :
    lineReductionRealQuadratic hb e
        (r ⊗ₜ[ℤ] (Submodule.Quotient.mk x : ↥(isotropicLinePerp (L := L) e) ⧸
          isotropicLineKernel (L := L) e)) =
      r * r * (L.obj.pairing (x : L.obj.carrier) (x : L.obj.carrier) : ℝ) := by
  rw [lineReductionRealQuadratic, LinearMap.BilinMap.toQuadraticMap_apply,
    lineReductionReal_tmul_mk]

end RealReductionForm

/-! ## `(e^⊥/ℤe) ⊗[ℤ] ℝ ≃ (e_ℝ)^⊥/⟨e_ℝ⟩` -/

section QuotientEquiv

variable [Module.Finite ℤ L.obj.carrier]

/-- **The quotient isometry's linear equivalence (#122)**: the base change of the reduction
`(e^⊥/ℤe) ⊗[ℤ] ℝ` is the real quotient `(e_ℝ)^⊥/⟨e_ℝ⟩`. Right exactness of `⊗` (Mathlib's
`TensorProduct.AlgebraTensorModule.tensorQuotientEquiv`, the `lTensor` cokernel form)
presents the left side as `(ℝ ⊗[ℤ] e^⊥) ⧸ range (lTensor ℝ of ℤe → e^⊥)`, and
`Submodule.Quotient.equiv` transports that quotient along `perpTensorEquiv` (#124) using
`map_range_isotropicLineKernel` (#124). -/
noncomputable def perpQuotientTensorEquiv (hb : L.obj.IsSymmetric) (e : L.obj.carrier)
    (he : L.obj.pairing e e = 0) :
    TensorProduct ℤ ℝ (↥(isotropicLinePerp (L := L) e) ⧸
      isotropicLineKernel (L := L) e) ≃ₗ[ℝ]
      (↥(linePerp (realQuadratic (L := L)) (toReal (L := L) e)) ⧸
        lineInPerp (realQuadratic (L := L)) (e := toReal (L := L) e)
          (realQuadratic_toReal e he)) :=
  (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv ℝ ℤ ℝ
      (isotropicLineKernel (L := L) e)).trans
    (Submodule.Quotient.equiv _ _ (perpTensorEquiv hb e)
      (map_range_isotropicLineKernel hb e he))

/-- The equivalence on a pure tensor: the class of `r ⊗ₜ x` is the class of the image of
`r ⊗ₜ x` under `perpTensorEquiv`. -/
theorem perpQuotientTensorEquiv_tmul_mk (hb : L.obj.IsSymmetric) (e : L.obj.carrier)
    (he : L.obj.pairing e e = 0) (r : ℝ) (x : ↥(isotropicLinePerp (L := L) e)) :
    perpQuotientTensorEquiv hb e he (r ⊗ₜ[ℤ] Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (perpTensorEquiv hb e (r ⊗ₜ[ℤ] x)) :=
  rfl

end QuotientEquiv

/-! ## The isometry of the induced forms -/

section Isometry

variable [Module.Finite ℤ L.obj.carrier]

/-- The image of the hyperbolic partner of `e` in the real form partners the image of `e`. -/
theorem associated_realQuadratic_pair (hb : L.obj.IsSymmetric) (e f : L.obj.carrier)
    (hB : L.obj.pairing e f = 1) :
    QuadraticMap.associated (realQuadratic (L := L)) (toReal (L := L) e) (toReal (L := L) f)
      = 1 := by
  rw [associated_realQuadratic hb, realPairing_tmul, hB]
  norm_num

omit [Module.Finite ℤ ↑L.obj.carrier] in
/-- The real form of the induced form is symmetric, from the symmetry of the pairing. -/
theorem lineReductionReal_symm (hb : L.obj.IsSymmetric) (e : L.obj.carrier)
    (x y : TensorProduct ℤ ℝ (↥(isotropicLinePerp (L := L) e) ⧸
      isotropicLineKernel (L := L) e)) :
    lineReductionReal hb e x y = lineReductionReal hb e y x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul s b =>
        induction b using Submodule.Quotient.induction_on with
        | _ b =>
          rw [lineReductionReal_tmul_mk, lineReductionReal_tmul_mk, hb, mul_comm r]
      | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

omit [Module.Finite ℤ ↑L.obj.carrier] in
/-- The associated bilinear form of the real quadratic form of the reduction is the real form of
the induced form. -/
theorem associated_lineReductionRealQuadratic (hb : L.obj.IsSymmetric) (e : L.obj.carrier) :
    QuadraticMap.associated (lineReductionRealQuadratic (L := L) hb e) =
      lineReductionReal (L := L) hb e :=
  QuadraticMap.associated_left_inverse (S := ℝ) (lineReductionReal_symm hb e)

/-- The associated bilinear form of the quotient form computes on classes: it is the restriction
of the real pairing. The polar formula reduces this to the induction formula
`isotropicQuotientForm_mk` for the values. -/
theorem associated_isotropicQuotientForm_mk (hb : L.obj.IsSymmetric) (e f : L.obj.carrier)
    (he : L.obj.pairing e e = 0) (hf : L.obj.pairing f f = 0) (hB : L.obj.pairing e f = 1)
    (u v : ↥(linePerp (realQuadratic (L := L)) (toReal (L := L) e))) :
    QuadraticMap.associated
        (isotropicQuotientForm (realQuadratic (L := L)) (realQuadratic_toReal e he)
          (realQuadratic_toReal f hf) (associated_realQuadratic_pair hb e f hB))
        (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      realPairing (L := L) (u : TensorProduct ℤ ℝ L.obj.carrier)
        (v : TensorProduct ℤ ℝ L.obj.carrier) := by
  rw [QuadraticMap.associated_apply, ← Submodule.Quotient.mk_add, isotropicQuotientForm_mk,
    isotropicQuotientForm_mk, isotropicQuotientForm_mk, ← associated_realQuadratic hb,
    QuadraticMap.associated_apply]
  rfl

/-- **The bilinear transport of the isometry (#122)**: the associated bilinear form of the real
quotient form, pulled back along the quotient equivalence, is the real form of the induced form.
Being bilinear, this is proved on pure tensors and extended additively in each argument. -/
theorem associated_isotropicQuotientForm_perpQuotientTensorEquiv
    (hb : L.obj.IsSymmetric) (e f : L.obj.carrier) (he : L.obj.pairing e e = 0)
    (hf : L.obj.pairing f f = 0) (hB : L.obj.pairing e f = 1)
    (y z : TensorProduct ℤ ℝ (↥(isotropicLinePerp (L := L) e) ⧸
      isotropicLineKernel (L := L) e)) :
    QuadraticMap.associated
        (isotropicQuotientForm (realQuadratic (L := L)) (realQuadratic_toReal e he)
          (realQuadratic_toReal f hf) (associated_realQuadratic_pair hb e f hB))
        (perpQuotientTensorEquiv hb e he y) (perpQuotientTensorEquiv hb e he z) =
      lineReductionReal (L := L) hb e y z := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s b =>
      induction a using Submodule.Quotient.induction_on with
      | _ a =>
        induction b using Submodule.Quotient.induction_on with
        | _ b =>
          rw [perpQuotientTensorEquiv_tmul_mk, perpQuotientTensorEquiv_tmul_mk,
            associated_isotropicQuotientForm_mk hb e f he hf hB, perpTensorEquiv_tmul,
            perpTensorEquiv_tmul, realPairing_tmul, lineReductionReal_tmul_mk]
    | add z₁ z₂ hz₁ hz₂ => simp [map_add, hz₁, hz₂]
  | add y₁ y₂ hy₁ hy₂ => simp [map_add, LinearMap.add_apply, hy₁, hy₂]

/-- **The isometry on elements (#122)**: the form the real quotient form induces, at the image of
an element under the quotient equivalence, is the value of the real quadratic form of the
reduction. Both sides are the diagonal of their associated bilinear forms
(`QuadraticMap.associated_eq_self_apply`), so the bilinear transport gives the equality. -/
theorem isotropicQuotientForm_perpQuotientTensorEquiv (hb : L.obj.IsSymmetric)
    (e f : L.obj.carrier) (he : L.obj.pairing e e = 0) (hf : L.obj.pairing f f = 0)
    (hB : L.obj.pairing e f = 1)
    (z : TensorProduct ℤ ℝ (↥(isotropicLinePerp (L := L) e) ⧸
      isotropicLineKernel (L := L) e)) :
    isotropicQuotientForm (realQuadratic (L := L)) (realQuadratic_toReal e he)
        (realQuadratic_toReal f hf) (associated_realQuadratic_pair hb e f hB)
        (perpQuotientTensorEquiv hb e he z) =
      lineReductionRealQuadratic (L := L) hb e z := by
  rw [← QuadraticMap.associated_eq_self_apply ℝ (lineReductionRealQuadratic (L := L) hb e) z,
    associated_lineReductionRealQuadratic hb e, ← QuadraticMap.associated_eq_self_apply ℝ
      (isotropicQuotientForm (realQuadratic (L := L)) (realQuadratic_toReal e he)
        (realQuadratic_toReal f hf) (associated_realQuadratic_pair hb e f hB))
      (perpQuotientTensorEquiv hb e he z)]
  exact associated_isotropicQuotientForm_perpQuotientTensorEquiv hb e f he hf hB z z

/-- **The quotient isometry (#122)**: the base change of the reduction is an isometry of the
induced forms. The linear equivalence transports the real form of the reduction to the form
`Q` induces on the real quotient; on pure tensors both sides are `r * r * (b(x, x) : ℝ)`. -/
noncomputable def lineReductionRealIsometryEquiv (hb : L.obj.IsSymmetric) (e f : L.obj.carrier)
    (he : L.obj.pairing e e = 0) (hf : L.obj.pairing f f = 0) (hB : L.obj.pairing e f = 1) :
    QuadraticMap.IsometryEquiv (lineReductionRealQuadratic (L := L) hb e)
      (isotropicQuotientForm (realQuadratic (L := L)) (realQuadratic_toReal e he)
        (realQuadratic_toReal f hf) (associated_realQuadratic_pair hb e f hB)) where
  toLinearEquiv := perpQuotientTensorEquiv hb e he
  map_app' := isotropicQuotientForm_perpQuotientTensorEquiv hb e f he hf hB

/-- The real form of the reduction is equivalent to the form `Q` induces on the real quotient. -/
theorem equivalent_lineReductionRealQuadratic (hb : L.obj.IsSymmetric) (e f : L.obj.carrier)
    (he : L.obj.pairing e e = 0) (hf : L.obj.pairing f f = 0) (hB : L.obj.pairing e f = 1) :
    QuadraticMap.Equivalent (lineReductionRealQuadratic (L := L) hb e)
      (isotropicQuotientForm (realQuadratic (L := L)) (realQuadratic_toReal e he)
        (realQuadratic_toReal f hf) (associated_realQuadratic_pair hb e f hB)) :=
  ⟨lineReductionRealIsometryEquiv hb e f he hf hB⟩

end Isometry

/-! ## The signature of the reduction -/

section Signature

variable [Module.Finite ℤ L.obj.carrier]

/-- **The signature of `e^⊥/ℤe` is the #119 signature of the real quotient**: the positive index
of the real form of the reduction, plus one, is the positive index of the real form of `L`. -/
theorem sigPos_lineReductionRealQuadratic (hb : L.obj.IsSymmetric) (e f : L.obj.carrier)
    (he : L.obj.pairing e e = 0) (hf : L.obj.pairing f f = 0) (hB : L.obj.pairing e f = 1) :
    sigPos (lineReductionRealQuadratic (L := L) hb e) + 1 =
      sigPos (realQuadratic (L := L)) := by
  rw [(equivalent_lineReductionRealQuadratic hb e f he hf hB).sigPos_eq]
  exact sigPos_isotropicQuotientForm (realQuadratic (L := L))
    (realQuadratic_toReal e he) (realQuadratic_toReal f hf)
    (associated_realQuadratic_pair hb e f hB)

/-- **The signature of `e^⊥/ℤe` is the #119 signature of the real quotient**: the negative index
of the real form of the reduction, plus one, is the negative index of the real form of `L`. -/
theorem sigNeg_lineReductionRealQuadratic (hb : L.obj.IsSymmetric) (e f : L.obj.carrier)
    (he : L.obj.pairing e e = 0) (hf : L.obj.pairing f f = 0) (hB : L.obj.pairing e f = 1) :
    sigNeg (lineReductionRealQuadratic (L := L) hb e) + 1 =
      sigNeg (realQuadratic (L := L)) := by
  rw [(equivalent_lineReductionRealQuadratic hb e f he hf hB).sigNeg_eq]
  exact sigNeg_isotropicQuotientForm (realQuadratic (L := L))
    (realQuadratic_toReal e he) (realQuadratic_toReal f hf)
    (associated_realQuadratic_pair hb e f hB)

end Signature

end LeanCategories.Lattices.Valued

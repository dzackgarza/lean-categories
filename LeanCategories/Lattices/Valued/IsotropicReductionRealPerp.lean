/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.IsotropicReductionBaseChange
public import LeanCategories.Lattices.Valued.IsotropicQuotientSignature
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# The real form of a lattice, the equivalence `e^⊥ ⊗[ℤ] ℝ ≃ (e_ℝ)^⊥`, and the real line (#124)

For an integral `ℤ`-lattice `L`, the base change `ℝ ⊗[ℤ] L.obj.carrier` carries the real form of
the pairing (`realPairing`, with quadratic refinement `realQuadratic`), the image `toReal` of a
lattice vector, and — for an isotropic `e` — the real orthogonal complement
`linePerp realQuadratic (toReal e)` and the real line `lineInPerp` of `e_ℝ` inside it, as the
specialization of `IsotropicQuotientSignature`'s `linePerp`/`lineInPerp` to the lattice's real
form.

`perpTensorEquiv` is the linear equivalence `ℝ ⊗[ℤ] e^⊥ ≃ (e_ℝ)^⊥`: `e^⊥` is the kernel of the
functional `b(e, ·)` (`isotropicLinePerp_eq_ker`), so its base change along `ℝ` is the kernel of
the tensored functional (Mathlib's `LinearMap.tensorKerEquiv`), and that kernel is the kernel of
the real functional `b(e_ℝ, ·)` (`ker_lTensor_eq_realFunctional`, `linePerp_realQuadratic_eq_ker`).

**The theorem of this module (#124)** is `map_range_isotropicLineKernel`: the equivalence carries
the range of `lTensor ℝ` of the inclusion `ℤe → e^⊥` onto the real line `ℝ · e_ℝ` inside
`(e_ℝ)^⊥`. This is the step of #122 that its quotient isometry
`(e^⊥/ℤe) ⊗[ℤ] ℝ ≃ (e_ℝ)^⊥/⟨e_ℝ⟩` needs before `Submodule.Quotient.equiv` applies.

The proof is an equality of submodules, not an element chase. The range of `lTensor ℝ` of the
inclusion is `Submodule.map` of the span of the single pure tensor `1 ⊗ [e]`
(`span_tmul_kernelClass_eq_top`: Mathlib's `TensorProduct.span_tmul_eq_top` upgrades from `ℤ` to
`ℝ` by `Submodule.span_eq_top_of_span_eq_top`, and `Submodule.span_le` reduces the inclusion to
generators, each an `ℤ`-multiple of the class of `e` by `exists_zsmul_kernelClass`); its image
under the equivalence is `Submodule.map_span` of the equivalence, and the generator is carried to
the generator (`perpTensorEquiv_rangeGenerator`).

The `ℤ`-action on the carrier is the bundled `ModuleCat.isModule` action (#123): the real form is
`ℝ ⊗[ℤ] L.obj.carrier`, Mathlib's base change, and no action is replaced. The `ZSMul`/module
diamonds that a `ℤ`-scalar meets when crossing a submodule coercion or a tensor are bridged by
`ModuleCat.zsmul_eq_smul` and `int_smul_eq_zsmul`, each stated once where it is used.

**Not here:** the quotient isometry of #122, and the induced form on `e^⊥/ℤe` it transports.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Izv. Akad.
  Nauk SSSR Ser. Mat. 43 (1979), §1: primitive isotropic vectors and the reduction `P^⊥/P`.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued
open scoped TensorProduct

namespace LeanCategories.Lattices.Valued

attribute [local instance 10000] Submodule.module

variable {L : IntegralLatticeCat ℤ}

/-! ## The real form: the functional `b(e, ·)` and its kernel -/

section RealForm

variable [Module.Finite ℤ L.obj.carrier]

/-- The image of an element of the lattice in its real form. -/
noncomputable abbrev toReal (x : L.obj.carrier) : TensorProduct ℤ ℝ L.obj.carrier :=
  (1 : ℝ) ⊗ₜ[ℤ] x

/-- The real form of the pairing. -/
noncomputable abbrev realPairing :
    LinearMap.BilinForm ℝ (TensorProduct ℤ ℝ L.obj.carrier) :=
  LinearMap.compr₂ (LinearMap.BilinMap.baseChange ℝ (L.obj.bilinMap))
    (TensorProduct.AlgebraTensorModule.rid ℤ ℝ ℝ).toLinearMap

/-- The real form of the quadratic form: `x ↦ b(x, x)`. -/
noncomputable abbrev realQuadratic : QuadraticForm ℝ (TensorProduct ℤ ℝ L.obj.carrier) :=
  LinearMap.BilinMap.toQuadraticMap (realPairing (L := L))

theorem realPairing_tmul (a b : ℝ) (x y : L.obj.carrier) :
    realPairing (L := L) (a ⊗ₜ[ℤ] x) (b ⊗ₜ[ℤ] y) = (a * b) * (L.obj.pairing x y : ℝ) := by
  simp [realPairing, BilinModuleCat.bilinMap, BilinModuleCat.adjoint,
    BilinModuleCat.pairing, Algebra.smul_def, mul_comm]

theorem realPairing_symm (hb : L.obj.IsSymmetric) (x y : TensorProduct ℤ ℝ L.obj.carrier) :
    realPairing (L := L) x y = realPairing (L := L) y x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b v => rw [realPairing_tmul, realPairing_tmul, hb, mul_comm a]
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- The functional `x ↦ b(e, x)` on the lattice. -/
noncomputable abbrev pairingLeft (e : L.obj.carrier) : L.obj.carrier →ₗ[ℤ] ℤ :=
  L.obj.bilinMap e

/-- The functional `b(e, ·)` on the real form, as a real-linear functional: the left tensor of
`b(e, ·)` with `ℝ`, with the values read in `ℝ`. -/
noncomputable abbrev realFunctional (e : L.obj.carrier) :
    TensorProduct ℤ ℝ L.obj.carrier →ₗ[ℝ] ℝ :=
  (TensorProduct.AlgebraTensorModule.rid ℤ ℝ ℝ).toLinearMap.comp
    (TensorProduct.AlgebraTensorModule.lTensor ℝ ℝ (pairingLeft (L := L) e))

theorem realFunctional_tmul (e : L.obj.carrier) (r : ℝ) (x : L.obj.carrier) :
    realFunctional (L := L) e (r ⊗ₜ[ℤ] x) = r * (L.obj.pairing e x : ℝ) := by
  simp [realFunctional, pairingLeft, BilinModuleCat.bilinMap_apply, mul_comm]

theorem realPairing_toReal_tmul (e : L.obj.carrier) (r : ℝ) (x : L.obj.carrier) :
    realPairing (L := L) (toReal (L := L) e) (r ⊗ₜ[ℤ] x) = r * (L.obj.pairing e x : ℝ) := by
  rw [realPairing_tmul]
  simp

/-- The two presentations of `b(e, ·)` on the real form agree. -/
theorem realPairing_toReal_eq (e : L.obj.carrier) :
    realPairing (L := L) (toReal (L := L) e) = realFunctional (L := L) e := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rw [realPairing_toReal_tmul, realFunctional_tmul]
  | add z w hz hw => rw [map_add, map_add, hz, hw]

theorem realQuadratic_toReal (e : L.obj.carrier) (he : L.obj.pairing e e = 0) :
    realQuadratic (L := L) (toReal (L := L) e) = 0 := by
  rw [realQuadratic, LinearMap.BilinMap.toQuadraticMap_apply, realPairing_toReal_tmul, he]
  simp

/-- The associated bilinear form of the real quadratic form is the real pairing. -/
theorem associated_realQuadratic (hb : L.obj.IsSymmetric) :
    QuadraticMap.associated (realQuadratic (L := L)) = realPairing (L := L) :=
  QuadraticMap.associated_left_inverse (S := ℝ) (realPairing_symm hb)

/-- **`(e_ℝ)^⊥` is the kernel of `b(e, ·)`.** -/
theorem linePerp_realQuadratic_eq_ker (hb : L.obj.IsSymmetric) (e : L.obj.carrier) :
    linePerp (realQuadratic (L := L)) (toReal (L := L) e) =
      LinearMap.ker (realFunctional (L := L) e) := by
  ext z
  rw [mem_linePerp_iff, associated_realQuadratic hb, realPairing_toReal_eq, LinearMap.mem_ker]

end RealForm

/-! ## `e^⊥ ⊗[ℤ] ℝ ≃ (e_ℝ)^⊥` -/

section BaseChange

variable [Module.Finite ℤ L.obj.carrier]

/-- `e^⊥` is the kernel of the functional `b(e, ·)`. -/
theorem isotropicLinePerp_eq_ker (e : L.obj.carrier) :
    isotropicLinePerp (L := L) e = LinearMap.ker (pairingLeft (L := L) e) := by
  ext x
  rw [isotropicLinePerp, BilinModuleCat.mem_orthogonalSubmodule_iff, LinearMap.mem_ker,
    pairingLeft, BilinModuleCat.bilinMap_apply]
  exact ⟨fun h => h e (Submodule.mem_span_singleton_self e), fun h p hp => by
    obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hp
    rw [BilinModuleCat.pairing_smul_left, h, smul_zero]⟩

/-- Scalar extension carries an equality of submodules to an equality of the tensor products. -/
noncomputable def tensorAlgebraCongr {p q : Submodule ℤ L.obj.carrier} (h : p = q) :
    TensorProduct ℤ ℝ ↥p ≃ₗ[ℝ] TensorProduct ℤ ℝ ↥q :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℝ ℝ) (LinearEquiv.ofEq p q h)

theorem ker_lTensor_eq_realFunctional (e : L.obj.carrier) :
    LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor ℝ ℝ (pairingLeft (L := L) e)) =
      LinearMap.ker (realFunctional (L := L) e) := by
  ext z
  rw [LinearMap.mem_ker, LinearMap.mem_ker, realFunctional, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  constructor
  · intro hz
    rw [hz, map_zero]
  · intro hz
    exact (TensorProduct.AlgebraTensorModule.rid ℤ ℝ ℝ).injective (by simpa using hz)

/-- **`e^⊥ ⊗[ℤ] ℝ ≃ (e_ℝ)^⊥`**: base change of the kernel of `b(e, ·)` along the flat
`ℤ`-module `ℝ`. -/
noncomputable def perpTensorEquiv (hb : L.obj.IsSymmetric) (e : L.obj.carrier) :
    TensorProduct ℤ ℝ ↥(isotropicLinePerp (L := L) e) ≃ₗ[ℝ]
      ↥(linePerp (realQuadratic (L := L)) (toReal (L := L) e)) :=
  ((tensorAlgebraCongr (L := L) (isotropicLinePerp_eq_ker (L := L) e)).trans
    (LinearMap.tensorKerEquiv (S := ℝ) (M := ℝ) (pairingLeft (L := L) e))).trans
    (LinearEquiv.ofEq _ _
      ((ker_lTensor_eq_realFunctional (L := L) e).trans
        (linePerp_realQuadratic_eq_ker hb e).symm))

/-- Scalar extension of a submodule identity, on a pure tensor. -/
theorem tensorAlgebraCongr_tmul {p q : Submodule ℤ L.obj.carrier} (h : p = q) (r : ℝ)
    (x : ↥p) :
    tensorAlgebraCongr (L := L) h (r ⊗ₜ[ℤ] x) =
      r ⊗ₜ[ℤ] (LinearEquiv.ofEq p q h x) := by
  simp [tensorAlgebraCongr]

end BaseChange

/-! ## The image of the line `ℤe` under the base change of `e^⊥` -/

section RealLine

variable [Module.Finite ℤ L.obj.carrier]

/-- The value of the real equivalence on a pure tensor: the inclusion. -/
theorem perpTensorEquiv_tmul (hb : L.obj.IsSymmetric) (e : L.obj.carrier)
    (r : ℝ) (x : ↥(isotropicLinePerp (L := L) e)) :
    ((perpTensorEquiv hb e (r ⊗ₜ[ℤ] x) :
        ↥(linePerp (realQuadratic (L := L)) (toReal (L := L) e))) :
      TensorProduct ℤ ℝ L.obj.carrier) = r ⊗ₜ[ℤ] (x : L.obj.carrier) := by
  rw [perpTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearMap.tensorKerEquiv_apply, tensorAlgebraCongr_tmul]
  change ((LinearMap.tensorKer ℝ ℝ (pairingLeft (L := L) e))
    (r ⊗ₜ[ℤ] (LinearEquiv.ofEq _ _ (isotropicLinePerp_eq_ker (L := L) e) x)) :
      TensorProduct ℤ ℝ L.obj.carrier) = r ⊗ₜ[ℤ] (x : L.obj.carrier)
  rw [LinearMap.tensorKer_tmul]
  rfl

/-- The class of `e` in the kernel of the reduction. -/
theorem mem_isotropicLineKernel_self (e : L.obj.carrier) (he : L.obj.pairing e e = 0) :
    (⟨e, mem_isotropicLinePerp (L := L) e he⟩ : ↥(isotropicLinePerp (L := L) e)) ∈
      isotropicLineKernel (L := L) e :=
  (mem_isotropicLineKernel_iff e _).mpr (Submodule.mem_span_singleton_self e)

/-- The generator `⟨e_ℝ⟩` of the line in the real orthogonal complement. -/
noncomputable abbrev realLineGenerator (e : L.obj.carrier) (he : L.obj.pairing e e = 0) :
    ↥(linePerp (realQuadratic (L := L)) (toReal (L := L) e)) :=
  ⟨toReal (L := L) e, mem_linePerp_self (realQuadratic_toReal e he)⟩

theorem lineInPerp_eq_span_realLineGenerator (e : L.obj.carrier)
    (he : L.obj.pairing e e = 0) :
    lineInPerp (realQuadratic (L := L)) (e := toReal (L := L) e) (realQuadratic_toReal e he) =
      Submodule.span ℝ {realLineGenerator e he} :=
  rfl

/-- The class of `e` in the kernel of the reduction, as a subtype element. -/
noncomputable abbrev kernelClass (e : L.obj.carrier) (he : L.obj.pairing e e = 0) :
    ↥(isotropicLineKernel (L := L) e) :=
  ⟨⟨e, mem_isotropicLinePerp (L := L) e he⟩, mem_isotropicLineKernel_self e he⟩

/-- The generator `v₀ = 1 ⊗ [e]` of the lTensor range as an ℝ-submodule. -/
noncomputable abbrev rangeGenerator (e : L.obj.carrier) (he : L.obj.pairing e e = 0) :
    TensorProduct ℤ ℝ ↥(isotropicLinePerp (L := L) e) :=
  (1 : ℝ) ⊗ₜ[ℤ] (kernelClass e he : ↥(isotropicLinePerp (L := L) e))

theorem rangeGenerator_mem (e : L.obj.carrier) (he : L.obj.pairing e e = 0) :
    rangeGenerator e he ∈ LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor ℝ ℝ
        (isotropicLineKernel (L := L) e).subtype) := by
  exact ⟨(1 : ℝ) ⊗ₜ[ℤ] kernelClass e he, rfl⟩

/-- Every element of the kernel line `ℤe ⊆ e^⊥` is an integer multiple of the class of `e`. The
two `ℤ`-actions on the submodule carriers (`ZSMul` of the additive group and the inherited
`Submodule.module` action) agree by #123; `ModuleCat.zsmul_eq_smul` bridges them at the carrier,
and the coercion facts are stated once, here. -/
theorem exists_zsmul_kernelClass (e : L.obj.carrier) (he : L.obj.pairing e e = 0)
    (n : ↥(isotropicLineKernel (L := L) e)) :
    ∃ z : ℤ, n = z • kernelClass e he := by
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp
    ((mem_isotropicLineKernel_iff e (n : ↥(isotropicLinePerp (L := L) e))).mp n.2)
  refine ⟨z, Subtype.ext ?_⟩
  have hc : ((z • kernelClass e he : ↥(isotropicLineKernel (L := L) e)) :
      ↥(isotropicLinePerp (L := L) e)) = z • ((kernelClass e he :
      ↥(isotropicLineKernel (L := L) e)) : ↥(isotropicLinePerp (L := L) e)) := rfl
  rw [hc]
  refine Subtype.ext ?_
  have hc2 : (((z • ((kernelClass e he : ↥(isotropicLineKernel (L := L) e)) :
      ↥(isotropicLinePerp (L := L) e))) : ↥(isotropicLinePerp (L := L) e)) :
      L.obj.carrier) = z • (((kernelClass e he : ↥(isotropicLineKernel (L := L) e)) :
      ↥(isotropicLinePerp (L := L) e)) : L.obj.carrier) := rfl
  rw [hc2]
  rw [show (((kernelClass e he : ↥(isotropicLineKernel (L := L) e)) :
    ↥(isotropicLinePerp (L := L) e)) : L.obj.carrier) = e from rfl,
    ModuleCat.zsmul_eq_smul]
  exact hz.symm

/-- **The base change of the kernel line to `ℝ` is generated by `1 ⊗ [e]`**: the real tensor
product `ℝ ⊗[ℤ] (ℤe ⊆ e^⊥)` is spanned, over `ℝ`, by the single pure tensor `1 ⊗ [e]`. The
`ℤ`-scalar of a generator crosses the tensor by `TensorProduct.tmul_smul`, with the
`ZSMul`/module-action diamond on the carrier bridged by `int_smul_eq_zsmul` (#123). -/
theorem span_tmul_kernelClass_eq_top (e : L.obj.carrier) (he : L.obj.pairing e e = 0) :
    Submodule.span ℝ {(1 : ℝ) ⊗ₜ[ℤ] kernelClass e he} = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← Submodule.span_eq_top_of_span_eq_top ℤ ℝ _
    (TensorProduct.span_tmul_eq_top ℤ ℝ ↥(isotropicLineKernel (L := L) e))]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, n, rfl⟩
  obtain ⟨z, hz⟩ := exists_zsmul_kernelClass e he n
  have hval : m ⊗ₜ[ℤ] n = (m * (z : ℝ)) • ((1 : ℝ) ⊗ₜ[ℤ] kernelClass e he) := by
    rw [hz]
    have hint : (inferInstance : Module ℤ ↥(isotropicLineKernel (L := L) e)).smul z
        (kernelClass e he) = z • kernelClass e he :=
      int_smul_eq_zsmul _ z (kernelClass e he)
    have hstep : m ⊗ₜ[ℤ]
        ((inferInstance : Module ℤ ↥(isotropicLineKernel (L := L) e)).smul z
          (kernelClass e he)) = (z • m) ⊗ₜ[ℤ] kernelClass e he :=
      TensorProduct.tmul_smul z m (kernelClass e he)
    rw [← hint, hstep, zsmul_eq_mul, mul_comm,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hval]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The equivalence `perpTensorEquiv` carries the generator of the lTensor range to the
generator of the real line. -/
theorem perpTensorEquiv_rangeGenerator (hb : L.obj.IsSymmetric) (e : L.obj.carrier)
    (he : L.obj.pairing e e = 0) :
    perpTensorEquiv hb e (rangeGenerator e he) = realLineGenerator e he := by
  refine Subtype.ext ?_
  rw [perpTensorEquiv_tmul hb e (1 : ℝ)
    (kernelClass e he : ↥(isotropicLinePerp (L := L) e))]

/-- **The image of the lTensor range under the real equivalence is the real line (#124)**: the
base change `e^⊥ ⊗[ℤ] ℝ ≃ (e_ℝ)^⊥` carries the range of `lTensor ℝ` of the inclusion
`ℤe → e^⊥` onto the real line `ℝ · e_ℝ` inside `(e_ℝ)^⊥`. The equality of submodules is a chain
of `Submodule.map`/`span` rewrites: the range is `LinearMap.range_eq_map` of the top, the top is
the span of `1 ⊗ [e]` (`span_tmul_kernelClass_eq_top`), the image under the equivalence is
`Submodule.map_comp` and `Submodule.map_span` of the image of the generator, and the generator is
carried to the generator (`perpTensorEquiv_rangeGenerator`). -/
theorem map_range_isotropicLineKernel (hb : L.obj.IsSymmetric) (e : L.obj.carrier)
    (he : L.obj.pairing e e = 0) :
    (LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor ℝ ℝ
        (isotropicLineKernel (L := L) e).subtype)).map
        (perpTensorEquiv hb e).toLinearMap =
      lineInPerp (realQuadratic (L := L)) (e := toReal (L := L) e)
        (realQuadratic_toReal e he) := by
  rw [lineInPerp_eq_span_realLineGenerator e he, LinearMap.range_eq_map,
    ← span_tmul_kernelClass_eq_top e he, ← Submodule.map_comp, Submodule.map_span,
    Set.image_singleton]
  have hX : (perpTensorEquiv hb e).toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.lTensor ℝ ℝ
        (isotropicLineKernel (L := L) e).subtype) ((1 : ℝ) ⊗ₜ[ℤ] kernelClass e he)
      = realLineGenerator e he := by
    rw [LinearMap.comp_apply]
    exact perpTensorEquiv_rangeGenerator hb e he
  rw [hX]

end RealLine

end LeanCategories.Lattices.Valued

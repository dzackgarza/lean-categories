/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.ScaleAndEvenness
public import LeanCategories.Lattices.Valued.Sublattice
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]

/-- Every pairing value lies in the scale ideal. -/
theorem pairing_mem_scaleModule (L : IntegralLatticeCat R) (x y : L.obj.carrier) :
    L.obj.pairing x y ∈ scaleModule L :=
  ⟨x ⊗ₜ[R] y, rfl⟩

/-- The self-pairing of `v` generates every pairing value of the lattice. -/
def GeneratesScale (L : IntegralLatticeCat R) (v : L.obj.carrier) : Prop :=
  scaleModule L = Ideal.span {L.obj.pairing v v}

/-- A maximal-scale vector divides every pairing value. -/
theorem dvd_pairing_of_generatesScale (L : IntegralLatticeCat R) (v : L.obj.carrier)
    (hv : GeneratesScale L v) (x y : L.obj.carrier) :
    L.obj.pairing v v ∣ L.obj.pairing x y := by
  rw [← Ideal.mem_span_singleton, ← hv]
  exact pairing_mem_scaleModule L x y

section Existence

/-- The value ideal is contained in the scale ideal. -/
theorem valueModule_le_scaleModule (L : IntegralLatticeCat R) :
    valueModule L ≤ scaleModule L := by
  rw [valueModule, Ideal.span_le]
  rintro _ ⟨x, rfl⟩
  exact pairing_mem_scaleModule L x x

/-- With `2` invertible, polarization identifies the scale ideal with the value ideal. -/
theorem scaleModule_eq_valueModule [Invertible (2 : R)] (L : IntegralLatticeCat R) :
    scaleModule L = valueModule L :=
  le_antisymm
    ((isIIntegral_iff_scaleModule_le L (valueModule L)).mp
      (isIIntegral_of_isIEven_of_invertible_two L (valueModule L)
        ((isIEven_iff_valueModule_le L (valueModule L)).mpr le_rfl)))
    (valueModule_le_scaleModule L)

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- Over a discrete valuation ring with `2` invertible, some vector has maximal scale.

Its self-pairing is a diagonal value of least additive valuation, and every value is a
combination of diagonal values. -/
theorem exists_generatesScale [Invertible (2 : R)] (L : IntegralLatticeCat R) :
    ∃ v : L.obj.carrier, GeneratesScale L v := by
  obtain ⟨n, ⟨v, rfl⟩, hmin⟩ := (wellFounded_lt (α := ℕ∞)).has_min
    (Set.range fun x ↦ IsDiscreteValuationRing.addVal R (quadraticMap L x)) ⟨_, ⟨0, rfl⟩⟩
  refine ⟨v, ?_⟩
  have hdvd : ∀ x : L.obj.carrier, quadraticMap L v ∣ quadraticMap L x := by
    intro x
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd]
    exact not_lt.mp (hmin _ ⟨x, rfl⟩)
  rw [GeneratesScale, scaleModule_eq_valueModule, valueModule]
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ ⟨x, rfl⟩
    exact Ideal.mem_span_singleton.mpr (hdvd x)
  · rintro _ rfl
    exact Ideal.subset_span (Set.mem_range_self v)

end Existence

section Splitting

variable [IsDomain R] (L : IntegralLatticeCat R) (v : L.obj.carrier)
  (hv : GeneratesScale L v) (hne : L.obj.pairing v v ≠ 0)

include hne in
/-- Multiplication by the self-pairing of `v` is injective. -/
theorem injective_mul_pairing_self :
    Function.Injective (LinearMap.toSpanSingleton R R (L.obj.pairing v v)) := by
  intro a b hab
  exact mul_right_cancel₀ hne (by simpa [LinearMap.toSpanSingleton_apply, smul_eq_mul] using hab)

omit [IsDomain R] in
include hv in
/-- Pairing against `v` lands in the range of multiplication by `b(v,v)`. -/
theorem pairing_mem_range_toSpanSingleton (x : L.obj.carrier) :
    L.obj.pairing v x ∈
      LinearMap.range (LinearMap.toSpanSingleton R R (L.obj.pairing v v)) := by
  obtain ⟨c, hc⟩ := dvd_pairing_of_generatesScale L v hv v x
  exact ⟨c, by simpa [LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm] using hc.symm⟩

/-- The coefficient of the projection onto the line spanned by a maximal-scale vector.

Division by `b(v,v)` is well defined because that element generates the scale ideal and is
a non-zero-divisor. -/
noncomputable def scaleCoefficient : L.obj.carrier →ₗ[R] R :=
  (LinearEquiv.ofInjective _ (injective_mul_pairing_self L v hne)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (L.obj.adjoint v) (pairing_mem_range_toSpanSingleton L v hv)

/-- The projection coefficient recovers the pairing against `v`. -/
theorem pairing_self_mul_scaleCoefficient (x : L.obj.carrier) :
    L.obj.pairing v v * scaleCoefficient L v hv hne x = L.obj.pairing v x := by
  have h := congrArg Subtype.val
    ((LinearEquiv.ofInjective _ (injective_mul_pairing_self L v hne)).apply_symm_apply
      (LinearMap.codRestrict _ (L.obj.adjoint v)
        (pairing_mem_range_toSpanSingleton L v hv) x))
  simp only [LinearEquiv.ofInjective_apply, LinearMap.toSpanSingleton_apply, smul_eq_mul,
    LinearMap.codRestrict_apply] at h
  rw [mul_comm]
  exact h

/-- The projection coefficient of `v` itself is `1`. -/
theorem scaleCoefficient_self : scaleCoefficient L v hv hne v = 1 := by
  apply mul_left_cancel₀ hne
  rw [pairing_self_mul_scaleCoefficient, mul_one]

/-- Projection of a vector away from the line spanned by a maximal-scale vector. -/
noncomputable def maximalScaleProjection : L.obj.carrier →ₗ[R] L.obj.carrier :=
  LinearMap.id -
    LinearMap.toSpanSingleton R L.obj.carrier v ∘ₗ scaleCoefficient L v hv hne

@[simp]
theorem maximalScaleProjection_apply (x : L.obj.carrier) :
    maximalScaleProjection L v hv hne x = x - scaleCoefficient L v hv hne x • v :=
  rfl

/-- The projection is orthogonal to `v`. -/
theorem pairing_maximalScaleProjection (x : L.obj.carrier) :
    L.obj.pairing v (maximalScaleProjection L v hv hne x) = 0 := by
  have hsub : maximalScaleProjection L v hv hne x
      = x + (-(scaleCoefficient L v hv hne x)) • v := by
    rw [maximalScaleProjection_apply, neg_smul, ← sub_eq_add_neg]
  have hmul := pairing_self_mul_scaleCoefficient L v hv hne x
  rw [hsub, BilinModuleCat.pairing_add_right, BilinModuleCat.pairing_smul_right,
    smul_eq_mul]
  linear_combination -hmul

/-- The projection lands in the orthogonal complement of the line spanned by `v`. -/
theorem maximalScaleProjection_mem_orthogonalSubmodule (x : L.obj.carrier) :
    maximalScaleProjection L v hv hne x ∈ orthogonalSubmodule L (R ∙ v) := by
  rw [mem_orthogonalSubmodule_iff]
  rintro p hp
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hp
  rw [BilinModuleCat.pairing_smul_left, pairing_maximalScaleProjection, smul_zero]

include hv hne in
/-- A maximal-scale vector splits its line off orthogonally.

This is the inductive step of Jordan decomposition over a local ring: the projection
`x ↦ x - (b(v,x)/b(v,v)) • v` is integral, so the line and its orthogonal complement are
complementary submodules. -/
theorem isCompl_span_singleton_orthogonalSubmodule :
    IsCompl (R ∙ v) (orthogonalSubmodule L (R ∙ v)) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxOrth
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have h0 : L.obj.pairing v (r • v) = 0 :=
      (mem_orthogonalSubmodule_iff L (R ∙ v) (r • v)).mp hxOrth v
        (Submodule.mem_span_singleton_self v)
    rw [BilinModuleCat.pairing_smul_right, smul_eq_mul] at h0
    rw [(mul_eq_zero.mp h0).resolve_right hne, zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.mpr
      ⟨scaleCoefficient L v hv hne x • v,
        Submodule.mem_span_singleton.mpr ⟨_, rfl⟩,
        maximalScaleProjection L v hv hne x,
        maximalScaleProjection_mem_orthogonalSubmodule L v hv hne x, ?_⟩
    rw [maximalScaleProjection_apply]
    abel

end Splitting

section LocalSplitting

variable [IsDomain R] [IsDiscreteValuationRing R] [Invertible (2 : R)]

/-- Over a discrete valuation ring with `2` invertible, a lattice with nonzero scale splits
off the line of a maximal-scale vector.

This is the engine of the Jordan decomposition: the complement carries the restricted form,
and its scale ideal is strictly smaller. -/
theorem exists_generatesScale_isCompl (L : IntegralLatticeCat R)
    (hL : scaleModule L ≠ ⊥) :
    ∃ v : L.obj.carrier, GeneratesScale L v ∧
      IsCompl (R ∙ v) (orthogonalSubmodule L (R ∙ v)) := by
  obtain ⟨v, hv⟩ := exists_generatesScale L
  have hne : L.obj.pairing v v ≠ 0 := by
    intro h0
    exact hL (hv.trans (Ideal.span_singleton_eq_bot.mpr h0))
  exact ⟨v, hv, isCompl_span_singleton_orthogonalSubmodule L v hv hne⟩

end LocalSplitting

end LeanCategories.Lattices.Valued

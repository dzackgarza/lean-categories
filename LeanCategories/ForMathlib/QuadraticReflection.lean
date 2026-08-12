/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Reflections of a quadratic space

Reflection in a vector of nonzero value, and the resulting transitivity: two vectors of
the same nonzero value lie in one orbit of the isometry group. That transitivity is the
vector case of Witt's extension theorem and the input to Witt cancellation.

The construction needs `2` invertible, so that a quadratic form is recovered from its
polar form.

Reference: Lam, *Introduction to Quadratic Forms over Fields*, Chapter I, §2.
-/

@[expose] public section

namespace LeanCategories.ForMathlib

open QuadraticMap

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- Reflection in a vector, as a linear map. It is an isometry when the vector has
nonzero value. -/
noncomputable def reflectionMap (w : V) : V →ₗ[K] V :=
  LinearMap.id -
    (LinearMap.toSpanSingleton K V ((Q w)⁻¹ • w)) ∘ₗ Q.polarBilin.flip w

theorem reflectionMap_apply (w x : V) :
    reflectionMap Q w x = x - ((Q w)⁻¹ * polar Q x w) • w := by
  simp [reflectionMap, LinearMap.toSpanSingleton_apply, smul_smul, polarBilin,
    mul_comm]

/-- The value of a vector shifted along a scalar multiple of another. -/
theorem map_sub_smul (c : K) (x w : V) :
    Q (x - c • w) = Q x + c * c * Q w - c * polar Q x w := by
  have h : Q (x + -(c • w)) = Q x + Q (-(c • w)) + polar Q x (-(c • w)) := by
    rw [QuadraticMap.polar]; ring
  rw [sub_eq_add_neg, h, Q.map_neg, QuadraticMap.map_smul, polar_neg_right,
    polar_smul_right, smul_eq_mul]
  ring

/-- The polar form against the reflecting vector changes sign. -/
theorem polar_reflectionMap (w x : V) (hw : Q w ≠ 0) :
    polar Q (reflectionMap Q w x) w = -polar Q x w := by
  rw [reflectionMap_apply, polar_sub_left, polar_smul_left, polar_self, smul_eq_mul,
    nsmul_eq_mul]
  field_simp
  ring

/-- Reflection is an isometry. -/
theorem apply_reflectionMap (w x : V) (hw : Q w ≠ 0) :
    Q (reflectionMap Q w x) = Q x := by
  rw [reflectionMap_apply, map_sub_smul]
  field_simp
  ring

theorem reflectionMap_apply_self (w : V) (hw : Q w ≠ 0) :
    reflectionMap Q w w = -w := by
  rw [reflectionMap_apply, polar_self, nsmul_eq_mul]
  field_simp
  module

theorem reflectionMap_involutive (w : V) (hw : Q w ≠ 0) (x : V) :
    reflectionMap Q w (reflectionMap Q w x) = x := by
  conv_lhs => rw [reflectionMap_apply Q w (reflectionMap Q w x),
    polar_reflectionMap Q w x hw, reflectionMap_apply]
  field_simp
  module

/-- Reflection in a vector of nonzero value. -/
noncomputable def reflection (w : V) (hw : Q w ≠ 0) : Q.IsometryEquiv Q where
  toLinearEquiv :=
    LinearEquiv.ofLinear (reflectionMap Q w) (reflectionMap Q w)
      (by ext x; exact reflectionMap_involutive Q w hw x)
      (by ext x; exact reflectionMap_involutive Q w hw x)
  map_app' x := apply_reflectionMap Q w x hw

@[simp]
theorem reflection_apply (w : V) (hw : Q w ≠ 0) (x : V) :
    reflection Q w hw x = x - ((Q w)⁻¹ * polar Q x w) • w :=
  reflectionMap_apply Q w x

theorem reflection_apply_self (w : V) (hw : Q w ≠ 0) :
    reflection Q w hw w = -w :=
  reflectionMap_apply_self Q w hw

/-- A vector whose polar against the reflecting vector is its value is shifted by it. -/
theorem reflectionMap_apply_of_polar_eq (w x : V) (hw : Q w ≠ 0)
    (h : polar Q x w = Q w) : reflectionMap Q w x = x - w := by
  rw [reflectionMap_apply, h, inv_mul_cancel₀ hw, one_smul]

theorem map_add_eq (x y : V) : Q (x + y) = Q x + Q y + polar Q x y := by
  rw [QuadraticMap.polar]; ring

theorem map_sub_eq (x y : V) : Q (x - y) = Q x + Q y - polar Q x y := by
  have h := map_sub_smul Q 1 x y
  simpa using h

section Transitive

variable [Invertible (2 : K)]

/-- Two vectors of the same nonzero value lie in one orbit of the isometry group.

This is the vector case of Witt's extension theorem, proved by reflecting in `u - v`, or
in `u + v` followed by `v` when the first reflection is unavailable. -/
theorem exists_isometryEquiv_apply_eq (u v : V) (hu : Q u ≠ 0) (huv : Q u = Q v) :
    ∃ σ : Q.IsometryEquiv Q, σ u = v := by
  have hv : Q v ≠ 0 := huv ▸ hu
  have hpolar_sub : polar Q u (u - v) = Q (u - v) := by
    rw [polar_sub_right, polar_self, map_sub_eq, nsmul_eq_mul, huv]
    ring
  have hpolar_add : polar Q u (u + v) = Q (u + v) := by
    rw [polar_add_right, polar_self, map_add_eq, nsmul_eq_mul, huv]
    ring
  by_cases hsub : Q (u - v) = 0
  · have hadd : Q (u + v) ≠ 0 := by
      intro hzero
      have hfour : Q (u - v) + Q (u + v) = 2 * (Q u + Q v) := by
        rw [map_sub_eq, map_add_eq]; ring
      rw [hsub, hzero, zero_add, ← huv] at hfour
      have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
      have hzero4 : (2 : K) * 2 * Q u = 0 := by
        rw [show (2 : K) * 2 * Q u = 2 * (Q u + Q u) by ring, ← hfour]
      exact hu ((mul_eq_zero.mp hzero4).resolve_left (mul_ne_zero h2 h2))
    refine ⟨(reflection Q (u + v) hadd).trans (reflection Q v hv), ?_⟩
    have h1 : reflection Q (u + v) hadd u = -v := by
      rw [show (reflection Q (u + v) hadd) u = reflectionMap Q (u + v) u from rfl,
        reflectionMap_apply_of_polar_eq Q (u + v) u hadd hpolar_add]
      abel
    change reflection Q v hv (reflection Q (u + v) hadd u) = v
    rw [h1, map_neg, reflection_apply_self]
    exact neg_neg v
  · refine ⟨reflection Q (u - v) hsub, ?_⟩
    rw [show (reflection Q (u - v) hsub) u = reflectionMap Q (u - v) u from rfl,
      reflectionMap_apply_of_polar_eq Q (u - v) u hsub hpolar_sub]
    abel

end Transitive

end LeanCategories.ForMathlib

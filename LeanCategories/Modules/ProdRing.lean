/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Prod

/-! # Modules over a product ring -/

@[expose] public section

namespace LinearEquiv

universe u

variable (A B M₁ M₂ N₁ N₂ : Type u)
variable [CommRing A] [CommRing B]
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N₁] [AddCommGroup N₂]
variable [Module A M₁] [Module B M₂] [Module A N₁] [Module B N₂]

local instance moduleProdLeft : Module (A × B) M₁ := Module.compHom M₁ (RingHom.fst A B)
local instance moduleProdRight : Module (A × B) M₂ := Module.compHom M₂ (RingHom.snd A B)
local instance moduleProdLeftTarget : Module (A × B) N₁ := Module.compHom N₁ (RingHom.fst A B)
local instance moduleProdRightTarget : Module (A × B) N₂ := Module.compHom N₂ (RingHom.snd A B)

private theorem left_smul (r : A) (x : M₁) : ((r, 0) : A × B) • x = r • x := rfl
private theorem leftTarget_smul (r : A) (x : N₁) : ((r, 0) : A × B) • x = r • x := rfl
private theorem right_smul (r : B) (x : M₂) : ((0, r) : A × B) • x = r • x := rfl
private theorem rightTarget_smul (r : B) (x : N₂) : ((0, r) : A × B) • x = r • x := rfl

private theorem left_annihilates_right (r : A) (x : M₂) : ((r, 0) : A × B) • x = 0 := by
  change (RingHom.snd A B (r, 0)) • x = 0
  simp

private theorem left_annihilates_rightTarget (r : A) (x : N₂) :
    ((r, 0) : A × B) • x = 0 := by
  change (RingHom.snd A B (r, 0)) • x = 0
  simp

private theorem right_annihilates_left (r : B) (x : M₁) : ((0, r) : A × B) • x = 0 := by
  change (RingHom.fst A B (0, r)) • x = 0
  simp

private theorem right_annihilates_leftTarget (r : B) (x : N₁) :
    ((0, r) : A × B) • x = 0 := by
  change (RingHom.fst A B (0, r)) • x = 0
  simp

/-- Equivalences of the two coordinates assemble over the product ring. -/
def prodRing (e₁ : M₁ ≃ₗ[A] N₁) (e₂ : M₂ ≃ₗ[B] N₂) :
    (M₁ × M₂) ≃ₗ[A × B] (N₁ × N₂) where
  toFun x := (e₁ x.1, e₂ x.2)
  invFun x := (e₁.symm x.1, e₂.symm x.2)
  map_add' x y := by simp
  map_smul' r x := by
    ext
    · exact e₁.map_smul r.1 x.1
    · exact e₂.map_smul r.2 x.2
  left_inv x := by simp
  right_inv x := by simp

/-- A product-ring equivalence restricts to its left coordinate. -/
def prodRingLeft (e : (M₁ × M₂) ≃ₗ[A × B] (N₁ × N₂)) : M₁ ≃ₗ[A] N₁ where
  toFun x := (e (x, 0)).1
  invFun x := (e.symm (x, 0)).1
  map_add' x y := by simpa using congrArg Prod.fst (e.map_add (x, 0) (y, 0))
  map_smul' r x := by
    have h := e.map_smul (r, 0) (x, 0)
    rw [Prod.smul_mk, left_smul, left_annihilates_right, Prod.smul_mk,
      leftTarget_smul, left_annihilates_rightTarget] at h
    exact congrArg Prod.fst h
  left_inv x := by
    have hs : e (x, 0) = ((e (x, 0)).1, 0) := by
      have h := e.map_smul ((1, 0) : A × B) (x, 0)
      rw [Prod.smul_mk, left_smul, one_smul, left_annihilates_right,
        Prod.smul_mk, leftTarget_smul, one_smul, left_annihilates_rightTarget] at h
      exact h
    change (e.symm ((e (x, 0)).1, 0)).1 = x
    rw [← hs, e.symm_apply_apply]
  right_inv x := by
    have hs : e.symm (x, 0) = ((e.symm (x, 0)).1, 0) := by
      have h := e.symm.map_smul ((1, 0) : A × B) (x, 0)
      rw [Prod.smul_mk, leftTarget_smul, one_smul, left_annihilates_rightTarget,
        Prod.smul_mk, left_smul, one_smul, left_annihilates_right] at h
      exact h
    change (e ((e.symm (x, 0)).1, 0)).1 = x
    rw [← hs, e.apply_symm_apply]

/-- A product-ring equivalence restricts to its right coordinate. -/
def prodRingRight (e : (M₁ × M₂) ≃ₗ[A × B] (N₁ × N₂)) : M₂ ≃ₗ[B] N₂ where
  toFun x := (e (0, x)).2
  invFun x := (e.symm (0, x)).2
  map_add' x y := by simpa using congrArg Prod.snd (e.map_add (0, x) (0, y))
  map_smul' r x := by
    have h := e.map_smul (0, r) (0, x)
    rw [Prod.smul_mk, right_annihilates_left, right_smul, Prod.smul_mk,
      right_annihilates_leftTarget, rightTarget_smul] at h
    exact congrArg Prod.snd h
  left_inv x := by
    have hs : e (0, x) = (0, (e (0, x)).2) := by
      have h := e.map_smul ((0, 1) : A × B) (0, x)
      rw [Prod.smul_mk, right_annihilates_left, right_smul, one_smul,
        Prod.smul_mk, right_annihilates_leftTarget, rightTarget_smul, one_smul] at h
      exact h
    change (e.symm (0, (e (0, x)).2)).2 = x
    rw [← hs, e.symm_apply_apply]
  right_inv x := by
    have hs : e.symm (0, x) = (0, (e.symm (0, x)).2) := by
      have h := e.symm.map_smul ((0, 1) : A × B) (0, x)
      rw [Prod.smul_mk, right_annihilates_leftTarget, rightTarget_smul, one_smul,
        Prod.smul_mk, right_annihilates_left, right_smul, one_smul] at h
      exact h
    change (e (0, (e.symm (0, x)).2)).2 = x
    rw [← hs, e.apply_symm_apply]

end LinearEquiv
